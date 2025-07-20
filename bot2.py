# Основные импорты Python
import os
import asyncio
import logging
import sys
import logging.handlers
import random
import re
import time
import shutil
import math
import socket
import secrets
from typing import List, Dict, Optional, Callable, Tuple, Union, Any
import json
import base64
import hashlib
from datetime import datetime, timedelta
from decimal import Decimal, InvalidOperation
from enum import Enum, auto
from dataclasses import dataclass
from pathlib import Path
from io import BytesIO
import sqlite3
from threading import Lock
from concurrent.futures import ThreadPoolExecutor

# Сторонние библиотеки
import aiosqlite
import argon2
import pyotp
import qrcode
from redis import Redis
from redis.exceptions import ConnectionError as RedisConnectionError
from dotenv import load_dotenv
from apscheduler.schedulers.background import BackgroundScheduler
from cryptography.fernet import Fernet, InvalidToken
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

# Импорты aiogram
from aiogram import Bot, Dispatcher, F, types
from aiogram.filters import Command, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.redis import RedisStorage
from aiogram.enums import ParseMode
from aiogram.types import (
    Message,
    KeyboardButton,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    CallbackQuery,
    BufferedInputFile
)
from aiogram.client.session.aiohttp import AiohttpSession

# Настройка логгера
def setup_logging(logs_dir: str):
    """Настройка системы логирования с ротацией логов"""
    logs_path = Path(logs_dir)
    logs_path.mkdir(parents=True, exist_ok=True)
    
    log_format = "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    log_file = logs_path / "bot.log"
    
    # Основной логгер
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    
    # Файловый обработчик с ротацией
    file_handler = logging.handlers.RotatingFileHandler(
        log_file,
        maxBytes=5*1024*1024,  # 5 MB
        backupCount=5,
        encoding='utf-8'
    )
    file_handler.setFormatter(logging.Formatter(log_format))
    logger.addHandler(file_handler)
    
    # Консольный обработчик
    console_handler = logging.StreamHandler()
    console_handler.setFormatter(logging.Formatter(log_format))
    logger.addHandler(console_handler)

load_dotenv()

# Константы
SECONDS_IN_DAY = 86400
SECONDS_IN_HOUR = 3600
MIN_PASSWORD_LENGTH = 12
MAX_PASSWORD_LENGTH = 128
MAX_WALLET_ADDRESS_LENGTH = 50
MIN_WALLET_ADDRESS_LENGTH = 20
MAX_LOGIN_ATTEMPTS = 5
LOCKOUT_TIME = 300  # 5 минут
MAX_USERNAME_LENGTH = 32
MAX_EMAIL_LENGTH = 255
MAX_PHONE_LENGTH = 20
MAX_SESSION_ID_LENGTH = 64
MAX_TOKEN_LENGTH = 128
MAX_IP_LENGTH = 45
MAX_USER_AGENT_LENGTH = 512
MAX_TRANSACTION_ID_LENGTH = 64
MAX_DESCRIPTION_LENGTH = 1000
MAX_TICKET_TEXT_LENGTH = 2000

class Config:
    """Конфигурация приложения с валидацией и загрузкой из переменных окружения"""
    
    def __init__(self):
        # Основные настройки бота
        self.BOT_TOKEN = self._get_env('BOT_TOKEN')
        self.ADMIN_IDS = self._parse_admin_ids(self._get_env('ADMIN_IDS', ''))
        self.APP_NAME = self._get_env('APP_NAME', 'SteamTopupBot')
        
        # Настройки Redis
        self.REDIS_URL = self._get_env('REDIS_URL', 'redis://localhost:6379/0')
        self.REDIS_POOL_SIZE = self._get_int('REDIS_POOL_SIZE', 10, 1, 50)
        
        # Настройки базы данных
        self.DB_PATH = self._normalize_path(self._get_env('DB_PATH', 'data/database.db'))
        self.BACKUP_DIR = self._normalize_path(self._get_env('BACKUP_DIR', 'data/backups'))
        self.LOGS_DIR = self._normalize_path(self._get_env('LOGS_DIR', 'data/logs'))
        
        # Настройки безопасности
        self.FERNET_KEY = self._get_fernet_key()
        self.PASSWORD_MIN_LENGTH = self._get_int('PASSWORD_MIN_LENGTH', MIN_PASSWORD_LENGTH, 8)
        self.MAX_LOGIN_ATTEMPTS = self._get_int('MAX_LOGIN_ATTEMPTS', MAX_LOGIN_ATTEMPTS, 1)
        self.LOCKOUT_TIME = self._get_int('LOCKOUT_TIME', LOCKOUT_TIME, 60)
        
        # Настройки платежей
        self.MIN_PAYMENT = self._get_decimal('MIN_PAYMENT', Decimal('10.0'), Decimal('0.01'))
        self.MAX_PAYMENT = self._get_decimal('MAX_PAYMENT', Decimal('50000.0'), self.MIN_PAYMENT)
        self.PAYMENT_COMMISSION = self._get_float('PAYMENT_COMMISSION', 0.05, 0.0, 0.5)  # 5%
        self.WITHDRAWAL_FEE = self._get_float('WITHDRAWAL_FEE', 0.03, 0.0, 0.5)  # 3%
        self.MAX_WITHDRAWAL = self._get_decimal('MAX_WITHDRAWAL', Decimal('100000.0'), self.MIN_PAYMENT)
        self.MAX_MANUAL_BALANCE_CHANGE = self._get_decimal('MAX_MANUAL_BALANCE_CHANGE', Decimal('10000.0'), Decimal('0.01'))
        
        # Настройки операционных лимитов
        self.PAYMENT_LIMIT = self._get_int('PAYMENT_LIMIT', 10, 1)
        self.PAYMENT_LIMIT_PERIOD = self._get_int('PAYMENT_LIMIT_PERIOD', 3600, 300)
        self.WITHDRAWAL_LIMIT = self._get_int('WITHDRAWAL_LIMIT', 5, 1)
        self.WITHDRAWAL_LIMIT_PERIOD = self._get_int('WITHDRAWAL_LIMIT_PERIOD', 86400, 3600)
        
        # Валидация конфигурации
        self._validate_config()
        self._create_directories()
        logging.info("Конфигурация успешно загружена")

    def _get_env(self, key: str, default: Optional[str] = None) -> str:
        """Получение значения переменной окружения"""
        value = os.getenv(key, default)
        if value is None:
            raise ValueError(f"Обязательная переменная {key} не установлена")
        return value

    def _parse_admin_ids(self, ids_str: str) -> List[int]:
        """Парсинг списка ID администраторов"""
        if not ids_str.strip():
            return []
        
        ids = []
        for id_str in ids_str.replace(',', ' ').split():
            try:
                ids.append(int(id_str.strip()))
            except ValueError:
                logging.warning(f"Некорректный ID администратора: {id_str}")
        return ids

    def _normalize_path(self, path: str) -> str:
        """Нормализация путей"""
        return str(Path(path).absolute())

    def _get_fernet_key(self) -> str:
        """Получение или генерация ключа шифрования"""
        key = self._get_env('FERNET_KEY', None)
        if key is None:
            key = Fernet.generate_key().decode()
            logging.warning("Сгенерирован новый ключ шифрования. Укажите FERNET_KEY в .env")
        return key

    def _get_int(self, key: str, default: int, min_val: Optional[int] = None, 
                max_val: Optional[int] = None) -> int:
        """Получение целочисленного значения с валидацией"""
        try:
            value = int(self._get_env(key, str(default)))
            if min_val is not None and value < min_val:
                raise ValueError(f"{key} должен быть ≥ {min_val}")
            if max_val is not None and value > max_val:
                raise ValueError(f"{key} должен быть ≤ {max_val}")
            return value
        except ValueError as e:
            raise ValueError(f"Некорректное значение для {key}: {e}")

    def _get_float(self, key: str, default: float, min_val: float, max_val: float) -> float:
        """Получение значения с плавающей точкой с валидацией"""
        try:
            value = float(self._get_env(key, str(default)))
            if value < min_val or value > max_val:
                raise ValueError(f"{key} должен быть в диапазоне от {min_val} до {max_val}")
            return value
        except ValueError as e:
            raise ValueError(f"Некорректное значение для {key}: {e}")

    def _get_decimal(self, key: str, default: Decimal, min_val: Optional[Decimal] = None) -> Decimal:
        """Получение десятичного значения с валидацией"""
        try:
            value = Decimal(self._get_env(key, str(default)))
            if min_val is not None and value < min_val:
                raise ValueError(f"{key} должен быть ≥ {min_val}")
            return value
        except Exception as e:
            raise ValueError(f"Некорректное значение для {key}: {e}")

    def _create_directories(self):
        """Создание всех необходимых директорий"""
        Path(self.DB_PATH).parent.mkdir(parents=True, exist_ok=True)
        Path(self.BACKUP_DIR).mkdir(parents=True, exist_ok=True)
        Path(self.LOGS_DIR).mkdir(parents=True, exist_ok=True)
        logging.info("Директории приложения созданы")

    def _validate_config(self):
        """Проверка корректности конфигурации"""
        if not isinstance(self.ADMIN_IDS, list):
            raise ValueError("ADMIN_IDS должен быть списком")
        
        if not (Decimal('0') < self.MIN_PAYMENT <= self.MAX_PAYMENT):
            raise ValueError("Некорректные лимиты платежей")
        
        if not self.REDIS_URL.startswith(('redis://', 'rediss://')):
            raise ValueError("Некорректный URL Redis")
        
        if self.PAYMENT_COMMISSION < 0 or self.PAYMENT_COMMISSION > 0.5:
            raise ValueError("Комиссия платежа должна быть между 0 и 0.5")
        
        if self.WITHDRAWAL_FEE < 0 or self.WITHDRAWAL_FEE > 0.5:
            raise ValueError("Комиссия вывода должна быть между 0 и 0.5")

    async def check_redis_connection(self) -> bool:
        """Проверка подключения к Redis"""
        try:
            redis_client = Redis.from_url(
                self.REDIS_URL, 
                socket_connect_timeout=5,
                max_connections=self.REDIS_POOL_SIZE
            )
            return redis_client.ping()
        except RedisConnectionError as e:
            logging.error(f"Ошибка подключения к Redis: {e}")
            return False
        except Exception as e:
            logging.error(f"Неизвестная ошибка при проверке Redis: {e}")
            return False

class ErrorLevel(Enum):
    """Уровни серьезности ошибок"""
    LOW = auto()
    MEDIUM = auto()
    HIGH = auto()
    CRITICAL = auto()

class ErrorCode(Enum):
    """Коды ошибок для системы обработки исключений"""
    DATABASE_CONNECTION_ERROR = 1001
    INVALID_INPUT = 1002
    RATE_LIMIT_EXCEEDED = 1003
    SECURITY_VIOLATION = 5001
    TRANSACTION_FAILED = 3001
    DATABASE_ERROR = 1004
    USERNAME_EXISTS = 2001
    WEAK_PASSWORD = 2002
    USER_NOT_FOUND = 2003
    ACCOUNT_LOCKED = 2004
    AUTH_FAILED = 2005
    INVALID_MFA_CODE = 2006
    PAYMENT_FAILED = 3002
    WITHDRAWAL_FAILED = 3003
    INSUFFICIENT_FUNDS = 3004
    PERMISSION_DENIED = 4001
    AUTH_REQUIRED = 4002
    OPERATION_LIMIT = 4003
    INVALID_AMOUNT = 4004
    INVALID_WALLET = 4005
    UNKNOWN_ERROR = 9999

@dataclass
class ErrorInfo:
    """Информация об ошибке"""
    code: int
    message: str
    user_message: str
    level: ErrorLevel
    retryable: bool
    notify_admin: bool

class BotError(Exception):
    """Класс ошибок бота"""
    
    def __init__(self, error_code: ErrorCode, details: str = "", user_id: Optional[int] = None):
        self.error_code = error_code
        self.details = details
        self.user_id = user_id
        self.timestamp = datetime.now()
        super().__init__(f"{error_code.name}: {details}")
    
    async def handle(self, bot: Optional[Bot] = None):
        """Обработка ошибки с отправкой пользователю понятного сообщения"""
        error_messages = {
            ErrorCode.DATABASE_CONNECTION_ERROR: "Ошибка подключения к базе данных",
            ErrorCode.INVALID_INPUT: "Некорректные входные данные",
            ErrorCode.RATE_LIMIT_EXCEEDED: "Слишком много запросов. Попробуйте позже",
            ErrorCode.SECURITY_VIOLATION: "Нарушение безопасности",
            ErrorCode.TRANSACTION_FAILED: "Ошибка транзакции",
            ErrorCode.DATABASE_ERROR: "Ошибка базы данных",
            ErrorCode.USERNAME_EXISTS: "Этот логин уже используется",
            ErrorCode.WEAK_PASSWORD: "Слабый пароль",
            ErrorCode.USER_NOT_FOUND: "Пользователь не найден",
            ErrorCode.ACCOUNT_LOCKED: "Аккаунт заблокирован",
            ErrorCode.AUTH_FAILED: "Ошибка авторизации",
            ErrorCode.INVALID_MFA_CODE: "Неверный код аутентификации",
            ErrorCode.PAYMENT_FAILED: "Ошибка платежа",
            ErrorCode.WITHDRAWAL_FAILED: "Ошибка вывода средств",
            ErrorCode.INSUFFICIENT_FUNDS: "Недостаточно средств",
            ErrorCode.PERMISSION_DENIED: "Доступ запрещен",
            ErrorCode.AUTH_REQUIRED: "Требуется авторизация",
            ErrorCode.OPERATION_LIMIT: "Превышен лимит операций",
            ErrorCode.INVALID_AMOUNT: "Некорректная сумма",
            ErrorCode.INVALID_WALLET: "Некорректный адрес кошелька",
            ErrorCode.UNKNOWN_ERROR: "Неизвестная ошибка",
        }
        
        error_message = error_messages.get(self.error_code, "Неизвестная ошибка")
        full_message = f"{error_message}"
        if self.details:
            full_message += f": {self.details[:200]}"
        
        logging.error(f"Ошибка {self.error_code.name}: {self.details}")
        
        if self.user_id and bot:
            try:
                await bot.send_message(
                    self.user_id,
                    f"⚠️ {full_message}"
                )
            except Exception as e:
                logging.error(f"Не удалось уведомить пользователя: {e}")
        
        critical_errors = {
            ErrorCode.SECURITY_VIOLATION,
            ErrorCode.DATABASE_CONNECTION_ERROR,
            ErrorCode.DATABASE_ERROR,
            ErrorCode.UNKNOWN_ERROR
        }
        
        if self.error_code in critical_errors and bot:
            admin_message = (
                f"🚨 КРИТИЧЕСКАЯ ОШИБКА\n"
                f"Код: {self.error_code.name}\n"
                f"Детали: {self.details[:300]}\n"
                f"Пользователь: {self.user_id or 'N/A'}\n"
                f"Время: {self.timestamp}"
            )
            
            logging.critical(admin_message)
            
            for admin_id in Config().ADMIN_IDS:
                try:
                    await bot.send_message(admin_id, admin_message)
                except Exception as e:
                    logging.error(f"Не удалось уведомить администратора {admin_id}: {e}")

class Database:
    """Полнофункциональный класс для работы с базой данных SQLite с асинхронным интерфейсом"""
    
    _instance = None
    _singleton_lock = Lock()
    
    def __new__(cls):
        with cls._singleton_lock:
            if cls._instance is None:
                cls._instance = super().__new__(cls)
                cls._instance._initialized = False
        return cls._instance
    
    def __init__(self):
        if self._initialized:
            return
            
        self._initialized = True
        self.config = Config()
        self.db_path = self.config.DB_PATH
        self.backup_dir = self.config.BACKUP_DIR
        self._connection = None
        self._connection_lock = asyncio.Lock()
        logging.info(f"Инициализация БД по пути: {self.db_path}")

    async def initialize(self):
        """Инициализация БД - создание таблиц, индексов и проверка соединения"""
        try:
            await self._create_connection()
            await self._create_tables()
            await self._create_indexes()
            await self._cleanup_old_sessions()
            logging.info("База данных успешно инициализирована")
        except Exception as e:
            logging.critical(f"Ошибка инициализации БД: {e}")
            traceback.print_exc()
            raise

    async def _create_connection(self):
        """Создание и настройка подключения к БД"""
        async with self._connection_lock:
            if self._connection is None:
                try:
                    Path(self.db_path).parent.mkdir(parents=True, exist_ok=True)
                    
                    self._connection = await aiosqlite.connect(self.db_path)
                    self._connection.row_factory = aiosqlite.Row
                    
                    await self._connection.execute("PRAGMA journal_mode=WAL")
                    await self._connection.execute("PRAGMA foreign_keys=ON")
                    await self._connection.execute("PRAGMA busy_timeout=5000")
                    await self._connection.execute("PRAGMA synchronous=NORMAL")
                    
                    logging.info(f"Подключение к БД установлено: {self.db_path}")
                except Exception as e:
                    logging.critical(f"Ошибка подключения к БД: {e}")
                    raise

    async def _create_tables(self):
        """Создание всех необходимых таблиц в БД"""
        tables = [
            # Таблица пользователей
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                username TEXT UNIQUE COLLATE NOCASE NOT NULL CHECK(LENGTH(username) <= 32),
                email TEXT UNIQUE CHECK(email IS NULL OR LENGTH(email) <= 255),
                phone TEXT UNIQUE CHECK(phone IS NULL OR LENGTH(phone) <= 20),
                password_hash TEXT NOT NULL CHECK(LENGTH(password_hash) <= 255),
                salt TEXT NOT NULL CHECK(LENGTH(salt) <= 64),
                is_active INTEGER DEFAULT 1 CHECK(is_active IN (0, 1)),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP,
                last_login TIMESTAMP,
                failed_login_attempts INTEGER DEFAULT 0 CHECK(failed_login_attempts >= 0),
                mfa_secret TEXT CHECK(mfa_secret IS NULL OR LENGTH(mfa_secret) <= 64),
                balance DECIMAL(15, 2) DEFAULT 0 CHECK(balance >= 0),
                role TEXT DEFAULT 'user' CHECK(LENGTH(role) <= 32)
            )
            """,
            # Таблица сессий
            """
            CREATE TABLE IF NOT EXISTS sessions (
                session_id TEXT PRIMARY KEY CHECK(LENGTH(session_id) <= 64),
                user_id INTEGER NOT NULL,
                token TEXT NOT NULL CHECK(LENGTH(token) <= 128),
                ip_address TEXT NOT NULL CHECK(LENGTH(ip_address) <= 45),
                user_agent TEXT CHECK(user_agent IS NULL OR LENGTH(user_agent) <= 512),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                expires_at TIMESTAMP NOT NULL,
                is_active INTEGER DEFAULT 1 CHECK(is_active IN (0, 1)),
                FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE
            )
            """,
            # Таблица транзакций
            """
            CREATE TABLE IF NOT EXISTS transactions (
                transaction_id TEXT PRIMARY KEY CHECK(LENGTH(transaction_id) <= 64),
                user_id INTEGER NOT NULL,
                amount DECIMAL(15, 2) NOT NULL CHECK(amount > 0),
                currency TEXT NOT NULL DEFAULT 'RUB' CHECK(LENGTH(currency) <= 3),
                status TEXT NOT NULL CHECK(LENGTH(status) <= 32),
                description TEXT CHECK(description IS NULL OR LENGTH(description) <= 1000),
                metadata TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                completed_at TIMESTAMP,
                type TEXT CHECK(type IS NULL OR LENGTH(type) <= 32),
                wallet_address TEXT CHECK(wallet_address IS NULL OR LENGTH(wallet_address) <= 50),
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """,
            # Таблица тикетов поддержки
            """
            CREATE TABLE IF NOT EXISTS support_tickets (
                ticket_id TEXT PRIMARY KEY CHECK(LENGTH(ticket_id) <= 64),
                user_id INTEGER NOT NULL,
                username TEXT NOT NULL CHECK(LENGTH(username) <= 32),
                text TEXT NOT NULL CHECK(LENGTH(text) <= 2000),
                status TEXT DEFAULT 'open' CHECK(LENGTH(status) <= 32),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                FOREIGN KEY(user_id) REFERENCES users(user_id)
            )
            """,
            # Таблица аудита
            """
            CREATE TABLE IF NOT EXISTS audit_log (
                log_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                action_type TEXT NOT NULL CHECK(LENGTH(action_type) <= 64),
                action_details TEXT CHECK(LENGTH(action_details) <= 1000),
                ip_address TEXT CHECK(LENGTH(ip_address) <= 45),
                user_agent TEXT CHECK(LENGTH(user_agent) <= 512),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE SET NULL
            )
            """
        ]
        
        try:
            for table_sql in tables:
                await self._connection.execute(table_sql)
            await self._connection.commit()
            logging.info("Таблицы успешно созданы")
        except Exception as e:
            logging.error(f"Ошибка создания таблиц: {e}")
            raise

    async def _create_indexes(self):
        """Создание индексов для оптимизации запросов"""
        indexes = [
            "CREATE INDEX IF NOT EXISTS idx_users_email ON users(email)",
            "CREATE INDEX IF NOT EXISTS idx_users_username ON users(username)",
            "CREATE INDEX IF NOT EXISTS idx_sessions_user ON sessions(user_id)",
            "CREATE INDEX IF NOT EXISTS idx_sessions_expires ON sessions(expires_at)",
            "CREATE INDEX IF NOT EXISTS idx_transactions_user ON transactions(user_id)",
            "CREATE INDEX IF NOT EXISTS idx_transactions_status ON transactions(status)",
            "CREATE INDEX IF NOT EXISTS idx_transactions_created ON transactions(created_at)",
            "CREATE INDEX IF NOT EXISTS idx_audit_log_user ON audit_log(user_id)",
            "CREATE INDEX IF NOT EXISTS idx_audit_log_created ON audit_log(created_at)"
        ]
        
        try:
            for index_sql in indexes:
                await self._connection.execute(index_sql)
            await self._connection.commit()
            logging.info("Индексы успешно созданы")
        except Exception as e:
            logging.error(f"Ошибка создания индексов: {e}")
            raise

    async def _cleanup_old_sessions(self):
        """Очистка устаревших сессий"""
        try:
            result = await self._connection.execute(
                "DELETE FROM sessions WHERE expires_at < datetime('now')"
            )
            await self._connection.commit()
            deleted_count = result.rowcount
            if deleted_count > 0:
                logging.info(f"Очистка старых сессий выполнена, удалено: {deleted_count} записей")
        except Exception as e:
            logging.error(f"Ошибка очистки сессий: {e}")

    async def execute(self, query: str, params: tuple = None, *, commit: bool = False) -> sqlite3.Cursor:
        """Выполнение SQL-запроса (INSERT, UPDATE, DELETE)"""
        try:
            cursor = await self._connection.execute(query, params or ())
            if commit:
                await self._connection.commit()
            return cursor
        except Exception as e:
            logging.error(f"Ошибка выполнения запроса: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, f"Ошибка выполнения запроса: {e}")

    async def fetch_one(self, query: str, params: tuple = None) -> Optional[dict]:
        """Получение одной записи"""
        try:
            cursor = await self._connection.execute(query, params or ())
            row = await cursor.fetchone()
            await cursor.close()
            return dict(row) if row else None
        except Exception as e:
            logging.error(f"Ошибка получения данных: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, f"Ошибка получения данных: {e}")

    async def fetch_all(self, query: str, params: tuple = None) -> List[dict]:
        """Получение всех записей"""
        try:
            cursor = await self._connection.execute(query, params or ())
            rows = await cursor.fetchall()
            await cursor.close()
            return [dict(row) for row in rows]
        except Exception as e:
            logging.error(f"Ошибка получения данных: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, f"Ошибка получения данных: {e}")

    async def backup(self) -> bool:
        """Создание резервной копии БД"""
        try:
            backup_dir = Path(self.backup_dir)
            backup_dir.mkdir(parents=True, exist_ok=True)
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            backup_path = backup_dir / f"backup_{timestamp}.db"
            
            async with aiosqlite.connect(self.db_path) as source:
                async with aiosqlite.connect(backup_path) as target:
                    await source.backup(target)
            
            logging.info(f"Резервная копия создана: {backup_path}")
            return True
        except Exception as e:
            logging.error(f"Ошибка создания резервной копии: {e}")
            return False

    async def create_transaction(self, data: dict):
        """Создание новой транзакции"""
        try:
            query = """
                INSERT INTO transactions (
                    transaction_id, user_id, amount, currency, status,
                    description, type, wallet_address
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """
            params = (
                data["transaction_id"],
                data["user_id"],
                float(data["amount"]),
                data.get("currency", "RUB"),
                data["status"],
                data.get("description", ""),
                data.get("type", "deposit"),
                data.get("wallet_address")
            )
            await self.execute(query, params, commit=True)
        except Exception as e:
            logging.error(f"Ошибка создания транзакции: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка создания транзакции")

    async def get_user(self, user_id: int) -> Optional[dict]:
        """Получение пользователя по ID"""
        return await self.fetch_one("SELECT * FROM users WHERE user_id = ?", (user_id,))
    
    async def has_active_session(self, user_id: int) -> bool:
        """Проверка активной сессии пользователя"""
        session = await self.fetch_one(
            "SELECT 1 FROM sessions WHERE user_id = ? AND expires_at > datetime('now') AND is_active = 1",
            (user_id,)
        )
        return bool(session)
    
    async def update_transaction_status(self, transaction_id: str, status: str):
        """Обновление статуса транзакции"""
        await self.execute(
            "UPDATE transactions SET status = ?, completed_at = datetime('now') WHERE transaction_id = ?",
            (status, transaction_id),
            commit=True
        )
    
    async def log_audit(self, user_id: Optional[int], action_type: str, action_details: str):
        """Логирование действия в аудит"""
        ip_address = 'unknown'
        user_agent = 'unknown'
        await self.execute(
            """INSERT INTO audit_log (user_id, action_type, action_details, ip_address, user_agent)
            VALUES (?, ?, ?, ?, ?)""",
            (user_id, action_type, action_details, ip_address, user_agent),
            commit=True
        )
    
    async def update_user(self, user_id: int, data: dict):
        """Обновление данных пользователя"""
        if not data:
            return
        
        set_fields = []
        values = []
        for key, value in data.items():
            set_fields.append(f"{key} = ?")
            values.append(value)
        
        values.append(user_id)
        query = f"UPDATE users SET {', '.join(set_fields)} WHERE user_id = ?"
        
        await self.execute(query, tuple(values), commit=True)

    async def close(self):
        """Корректное закрытие соединения с БД"""
        try:
            async with self._connection_lock:
                if self._connection:
                    await self._connection.close()
                    self._connection = None
                    logging.info("Соединение с БД закрыто")
        except Exception as e:
            logging.error(f"Ошибка при закрытии БД: {e}")

    def transaction(self):
        """Контекстный менеджер для выполнения транзакций"""
        return DatabaseTransaction(self)

class DatabaseTransaction:
    """Контекстный менеджер для транзакций БД"""
    
    def __init__(self, db):
        self.db = db
        self._tx = None

    async def __aenter__(self):
        """Начало транзакции"""
        if not self.db._connection:
            await self.db._create_connection()
        
        self._tx = await self.db._connection.cursor()
        await self._tx.execute("BEGIN")
        return self._tx

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Завершение транзакции с обработкой ошибок"""
        try:
            if exc_type is not None:
                await self._tx.execute("ROLLBACK")
                logging.error(f"Transaction rolled back due to error: {exc_val}", exc_info=True)
            else:
                await self._tx.execute("COMMIT")
        except Exception as e:
            logging.critical(f"CRITICAL TRANSACTION ERROR: {str(e)}")
            try:
                await self._tx.execute("ROLLBACK")
            except Exception as rollback_error:
                logging.error(f"Rollback failed: {rollback_error}")
            raise BotError(
                ErrorCode.DATABASE_ERROR,
                "Ошибка завершения транзакции",
                user_id=None
            )
        finally:
            await self._tx.close()
        
        return False
    """Контекстный менеджер для транзакций БД"""
    
    def __init__(self, db):
        self.db = db
        self._tx = None

    async def __aenter__(self):
        """Начало транзакции"""
        if not self.db._connection:
            await self.db._create_connection()
        
        self._tx = await self.db._connection.cursor()
        await self._tx.execute("BEGIN")
        return self._tx  # Возвращаем курсор напрямую

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Завершение транзакции с обработкой ошибок"""
        try:
            if exc_type is not None:
                await self._tx.execute("ROLLBACK")
                logging.error(f"Transaction rolled back due to error: {exc_val}", exc_info=True)
            else:
                await self._tx.execute("COMMIT")
        except Exception as e:
            logging.critical(f"CRITICAL TRANSACTION ERROR: {str(e)}")
            try:
                await self._tx.execute("ROLLBACK")
            except Exception as rollback_error:
                logging.error(f"Rollback failed: {rollback_error}")
            raise BotError(
                ErrorCode.DATABASE_ERROR,
                "Ошибка завершения транзакции",
                user_id=None
            )
        finally:
            await self._tx.close()
        
        return False

class SecurityException(Exception):
    """Исключение безопасности"""
    
    def __init__(self, message: str, code: str = "SECURITY_ERROR"):
        self.code = code
        self.message = message
        super().__init__(f"[{code}] {message}")

class AnomalyDetector:
    """Детектор аномалий для выявления подозрительной активности"""
    
    def __init__(self):
        self.baseline = self._establish_baseline()
        self.anomaly_threshold = 3.0  # Пороговое значение для обнаружения аномалий
    
    def _establish_baseline(self) -> dict:
        """Установка базовых показателей нормальной активности"""
        return {
            'login_attempts': 0.5,    # Среднее количество попыток входа в минуту
            'password_errors': 0.1,    # Среднее количество ошибок пароля
            'mfa_failures': 0.05,      # Среднее количество ошибок 2FA
            'payment_attempts': 0.2    # Среднее количество попыток платежей
        }
    
    def detect_anomalies(self, current_stats: dict) -> bool:
        """
        Обнаружение аномалий на основе текущей статистики
        Возвращает True при обнаружении подозрительной активности
        """
        try:
            deviations = {}
            for key in self.baseline:
                baseline_val = self.baseline[key]
                current_val = current_stats.get(key, 0)
                
                if baseline_val == 0:
                    deviations[key] = current_val * 100
                else:
                    deviations[key] = current_val / baseline_val
            
            max_deviation = max(deviations.values()) if deviations else 0
            
            logging.debug(
                f"Анализ аномалий: Текущие показатели: {current_stats}, "
                f"Отклонения: {deviations}, Макс. отклонение: {max_deviation}"
            )
            
            return max_deviation > self.anomaly_threshold
        except Exception as e:
            logging.error(f"Ошибка детектирования аномалий: {e}")
            return False
    """Комплексная система безопасности для защиты приложения"""
    
    def __init__(self, config: Config):
        self.config = config
        self.rate_limits = {}  # Счетчики ограничения скорости
        self.lockout_tracker = {}  # Трекер блокировок
        self._init_crypto()
        
        # Политика паролей
        self.password_policy = {
            'min_length': max(12, config.PASSWORD_MIN_LENGTH),
            'max_length': 128,
            'require_upper': True,
            'require_lower': True,
            'require_digit': True,
            'require_special': True,
            'block_common': True,
            'block_repeats': True,
            'block_sequences': True
        }
        
        self._common_passwords = None
        self._init_monitoring()
        logging.info("Система безопасности инициализирована")

    def _init_crypto(self):
        """Инициализация криптографических компонентов"""
        self.password_hasher = argon2.PasswordHasher(
            time_cost=3,
            memory_cost=65536,
            parallelism=4,
            hash_len=32,
            salt_len=16
        )
        
        try:
            self.cipher_suite = Fernet(self.config.FERNET_KEY.encode())
        except Exception as e:
            logging.critical(f"Ошибка инициализации шифрования: {e}")
            raise SecurityException("Ошибка инициализации системы шифрования")
        
        self.rng = secrets.SystemRandom()
    
    @property
    def common_passwords(self) -> set:
        """Ленивая загрузка списка распространенных паролей"""
        if self._common_passwords is None:
            self._common_passwords = self._load_common_passwords()
        return self._common_passwords
    
    def _load_common_passwords(self) -> set:
        """Загрузка списка распространенных паролей из файла"""
        try:
            security_dir = Path('security')
            security_dir.mkdir(parents=True, exist_ok=True)
            common_passwords_path = security_dir / 'common_passwords.txt'
            
            if not common_passwords_path.exists():
                default_passwords = self._get_default_common_passwords()
                with open(common_passwords_path, 'w', encoding='utf-8') as f:
                    f.write("\n".join(default_passwords))
                logging.info("Создан файл common_passwords.txt с базовыми паролями")
                return set(default_passwords)
            
            with open(common_passwords_path, 'r', encoding='utf-8') as f:
                passwords = {line.strip().lower() for line in f if line.strip()}
                
                if not passwords:
                    logging.warning("Файл common_passwords.txt пуст, используется базовый набор")
                    return self._get_default_common_passwords()
                    
                return passwords
        except Exception as e:
            logging.error(f"Ошибка загрузки списка паролей: {e}")
            return self._get_default_common_passwords()
    
    def _get_default_common_passwords(self) -> set:
        """Возвращает базовый набор распространенных паролей"""
        return {
            'password', '123456', 'qwerty', 'admin', 'welcome',
            '12345678', '111111', 'sunshine', 'iloveyou', 'password1',
            'admin123', 'letmein', 'monkey', 'football', '123123',
            '123456789', '1234567890', '12345', '1234', '1234567',
            'dragon', 'baseball', 'abc123', 'superman', 'master',
            'trustno1', 'access', 'flower', 'hello', 'solo',
            'secret', 'mustang', 'michael', 'shadow', 'jennifer',
            'jordan', '1111', 'asdfgh', '123qwe', 'qwerty123',
            '1q2w3e4r', 'qwertyuiop', 'passw0rd', 'starwars', 'freedom'
        }
    
    def _init_monitoring(self):
        """Инициализация систем мониторинга безопасности"""
        self.security_events = []
        self.anomaly_detector = AnomalyDetector()
        
        self.scheduler = BackgroundScheduler()
        self.scheduler.add_job(
            self._check_security_status,
            'interval',
            minutes=30,
            next_run_time=datetime.now() + timedelta(minutes=5)
        )
        self.scheduler.start()
        logging.info("Мониторинг безопасности активирован")

    def _check_security_status(self):
        """Периодическая проверка состояния безопасности"""
        try:
            logging.info("Запуск проверки состояния безопасности...")
            
            current_stats = {
                'login_attempts': random.randint(0, 10),
                'password_errors': random.randint(0, 5),
                'mfa_failures': random.randint(0, 3),
                'payment_attempts': random.randint(0, 7)
            }
            
            if self.anomaly_detector.detect_anomalies(current_stats):
                alert_msg = "Обнаружена подозрительная активность в системе безопасности!"
                logging.warning(alert_msg)
                self.alert_admins(f"⚠️ {alert_msg}")
            
            self._cleanup_expired_lockouts()
            self._rotate_security_logs()
            
            logging.info("Проверка безопасности завершена")
        except Exception as e:
            logging.error(f"Ошибка проверки безопасности: {e}")

    def _cleanup_expired_lockouts(self):
        """Очистка устаревших записей о блокировках"""
        now = time.time()
        expired_keys = [
            key for key, timestamp in self.lockout_tracker.items()
            if now - timestamp > self.config.LOCKOUT_TIME
        ]
        
        for key in expired_keys:
            del self.lockout_tracker[key]
        
        if expired_keys:
            logging.info(f"Очищено {len(expired_keys)} устаревших блокировок")

    def _rotate_security_logs(self):
        """Ротация логов безопасности при достижении лимита"""
        if len(self.security_events) > 1000:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            logs_dir = Path('security/logs')
            logs_dir.mkdir(parents=True, exist_ok=True)
            filename = logs_dir / f"security_events_{timestamp}.log"
            
            try:
                with open(filename, 'w', encoding='utf-8') as f:
                    for event in self.security_events:
                        f.write(json.dumps(event, ensure_ascii=False) + "\n")
                
                self.security_events.clear()
                logging.info(f"Логи безопасности сохранены в {filename}")
            except Exception as e:
                logging.error(f"Ошибка ротации логов безопасности: {e}")

    def hash_password(self, password: str) -> str:
        """Хеширование пароля с проверкой политики безопасности"""
        self._validate_password_policy(password)
        
        try:
            return self.password_hasher.hash(password)
        except argon2.exceptions.HashingError as e:
            logging.error(f"Ошибка хеширования пароля: {e}")
            raise SecurityException("Ошибка создания хеша пароля")
    
    def _validate_password_policy(self, password: str):
        """Проверка соответствия пароля политике безопасности"""
        if not isinstance(password, str):
            raise SecurityException("Пароль должен быть строкой")
        
        if len(password) < self.password_policy['min_length']:
            raise SecurityException(
                f"Пароль должен содержать не менее {self.password_policy['min_length']} символов"
            )
        
        if len(password) > self.password_policy['max_length']:
            raise SecurityException(
                f"Пароль должен содержать не более {self.password_policy['max_length']} символов"
            )
        
        if self.password_policy['require_upper'] and not re.search(r'[A-Z]', password):
            raise SecurityException("Пароль должен содержать заглавные буквы")
        
        if self.password_policy['require_lower'] and not re.search(r'[a-z]', password):
            raise SecurityException("Пароль должен содержать строчные буквы")
        
        if self.password_policy['require_digit'] and not re.search(r'\d', password):
            raise SecurityException("Пароль должен содержать цифры")
        
        if self.password_policy['require_special'] and not re.search(r'[!@#$%^&*(),.?":{}|<>]', password):
            raise SecurityException("Пароль должен содержать специальные символы")
        
        if self.password_policy['block_common'] and password.lower() in self.common_passwords:
            raise SecurityException("Пароль слишком распространен и ненадежен")
        
        if self.password_policy['block_repeats'] and re.search(r'(.)\1{2,}', password):
            raise SecurityException("Пароль содержит повторяющиеся символы")
        
        if self.password_policy['block_sequences'] and (
            re.search(r'123|234|345|456|567|678|789|890', password) or
            re.search(r'qwer|wert|erty|rtyu|tyui|yuio|uiop', password.lower())
        ):
            raise SecurityException("Пароль содержит простые последовательности символов")

    def verify_password(self, password: str, stored_hash: str) -> bool:
        """Проверка соответствия пароля хранимому хешу"""
        if not password or not stored_hash:
            return False
        
        start_time = time.monotonic()
        
        try:
            result = self.password_hasher.verify(stored_hash, password)
            
            if result and self.password_hasher.check_needs_rehash(stored_hash):
                self.log_security_event(
                    "password_rehash_needed",
                    "Password hash needs rehashing",
                    severity="medium"
                )
            
            return result
        except argon2.exceptions.VerifyMismatchError:
            elapsed = time.monotonic() - start_time
            self._detect_bruteforce_attempt(elapsed)
            return False
        except argon2.exceptions.InvalidHash as e:
            self.log_security_event(
                "invalid_hash_format",
                f"Invalid hash format during verification: {str(e)}",
                severity="high"
            )
            return False
        except Exception as e:
            self.log_security_event(
                "password_verification_error",
                f"Unexpected error: {str(e)}",
                severity="critical"
            )
            return False
    
    def _detect_bruteforce_attempt(self, verification_time: float):
        """Обнаружение возможной атаки перебора по времени верификации"""
        if verification_time < 0.1:
            self.log_security_event(
                "suspicious_verification_speed",
                f"Password verification too fast: {verification_time:.6f}s",
                severity="high"
            )
        
        if verification_time > 1.0:
            self.log_security_event(
                "suspicious_verification_speed",
                f"Password verification too slow: {verification_time:.6f}s",
                severity="high"
            )

    def generate_mfa_secret(self) -> str:
        """Генерация секретного ключа для двухфакторной аутентификации"""
        return pyotp.random_base32()

    def generate_mfa_qr(self, secret: str, username: str) -> BytesIO:
        """Генерация QR-кода для настройки двухфакторной аутентификации"""
        try:
            issuer_name = re.sub(r'\s+', '', self.config.APP_NAME)
            
            uri = pyotp.totp.TOTP(secret).provisioning_uri(
                name=username,
                issuer_name=issuer_name
            )
            
            qr = qrcode.QRCode(
                version=1,
                error_correction=qrcode.constants.ERROR_CORRECT_L,
                box_size=10,
                border=4,
            )
            qr.add_data(uri)
            qr.make(fit=True)
            
            img = qr.make_image(fill_color="black", back_color="white")
            buf = BytesIO()
            img.save(buf, format="PNG")
            buf.seek(0)
            
            return buf
        except Exception as e:
            logging.error(f"Ошибка генерации QR-кода: {e}")
            raise SecurityException("Ошибка генерации QR-кода для 2FA")

    def verify_mfa_code(self, secret: str, code: str, window: int = 1) -> bool:
        """Проверка кода двухфакторной аутентификации"""
        if not secret or not code:
            return False
        
        if not re.match(r'^\d{6}$', code):
            return False
        
        try:
            return pyotp.TOTP(secret).verify(code, valid_window=window)
        except Exception as e:
            logging.error(f"Ошибка проверки MFA кода: {e}")
            return False

    def encrypt_data(self, data: Union[str, dict]) -> str:
        """Шифрование конфиденциальных данных"""
        try:
            if isinstance(data, dict):
                data = json.dumps(data, ensure_ascii=False)
            
            encrypted = self.cipher_suite.encrypt(data.encode('utf-8'))
            return base64.urlsafe_b64encode(encrypted).decode('utf-8')
        except Exception as e:
            logging.error(f"Ошибка шифрования данных: {e}")
            raise SecurityException("Ошибка шифрования данных")

    def decrypt_data(self, encrypted_data: str) -> str:
        """Дешифрование данных"""
        try:
            encrypted_bytes = base64.urlsafe_b64decode(encrypted_data)
            return self.cipher_suite.decrypt(encrypted_bytes).decode('utf-8')
        except InvalidToken:
            self.log_security_event(
                "decryption_failed",
                "Invalid token during decryption",
                severity="high"
            )
            raise SecurityException("Ошибка дешифрования: неверный токен")
        except Exception as e:
            self.log_security_event(
                "decryption_error",
                f"Decryption failed: {str(e)}",
                severity="critical"
            )
            raise SecurityException(f"Ошибка дешифрования: {str(e)}")

    def check_rate_limit(self, identifier: str, action: str, max_attempts: int, period: int) -> bool:
        """Проверка ограничения скорости запросов"""
        key = f"{identifier}_{action}"
        now = time.time()
        
        if key in self.lockout_tracker:
            lockout_time = self.lockout_tracker[key]
            elapsed = now - lockout_time
            if elapsed < period:
                return False
            del self.lockout_tracker[key]
        
        if key not in self.rate_limits:
            self.rate_limits[key] = {
                'count': 1,
                'timestamp': now
            }
            return True
        
        if now - self.rate_limits[key]['timestamp'] > period:
            self.rate_limits[key] = {
                'count': 1,
                'timestamp': now
            }
            return True
        
        self.rate_limits[key]['count'] += 1
        
        if self.rate_limits[key]['count'] > max_attempts:
            self.lockout_tracker[key] = now
            self.log_security_event(
                "rate_limit_exceeded",
                f"Action: {action}, Identifier: {identifier}",
                severity="high"
            )
            return False
        
        return True

    def generate_secure_token(self, length: int = 32) -> str:
        """Генерация криптографически безопасного токена"""
        if length < 16:
            raise ValueError("Длина токена должна быть не менее 16 символов")
        return secrets.token_urlsafe(length)

    def validate_input(self, input_str: str, pattern: str, min_len: int = 1, max_len: int = 255) -> bool:
        """Комплексная валидация пользовательского ввода"""
        if not isinstance(input_str, str):
            return False
        if len(input_str) < min_len or len(input_str) > max_len:
            return False
        
        if not re.fullmatch(pattern, input_str):
            return False
        
        dangerous_patterns = [
            r';', r'--', r'/\*', r'\*/', r'xp_',
            r'<script>', r'</script>', r'javascript:',
            r'onload\s*=', r'onerror\s*=', r'expression\('
        ]
        
        for danger in dangerous_patterns:
            if re.search(danger, input_str, re.IGNORECASE):
                return False
        
        return True

    def validate_steam_login(self, login: str) -> bool:
        """Валидация Steam логина"""
        return self.validate_input(
            login,
            r'^[a-zA-Z][a-zA-Z0-9_]{2,31}$',
            min_len=3,
            max_len=32
        ) and not any(c in login for c in ['@', ' ', '"', "'", ';'])

    async def validate_email(self, email: str) -> bool:
        """Комплексная валидация email адреса"""
        if not re.match(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$', email):
            return False
        
        try:
            domain = email.split('@')[1]
            loop = asyncio.get_running_loop()
            await loop.getaddrinfo(domain, None)
            return True
        except (socket.gaierror, IndexError, ValueError):
            return False
        except Exception as e:
            logging.error(f"Ошибка проверки DNS для email: {e}")
            return False

    def validate_phone(self, phone: str) -> bool:
        """Валидация номера телефона"""
        return re.match(r'^\+?[1-9]\d{1,14}$', phone) is not None

    def validate_wallet_address(self, wallet: str) -> bool:
        """Валидация адреса криптовалютного кошелька"""
        return self.validate_input(
            wallet,
            r'^[a-zA-Z0-9]{20,50}$',
            min_len=MIN_WALLET_ADDRESS_LENGTH,
            max_len=MAX_WALLET_ADDRESS_LENGTH
        )

    def sanitize_input(self, input_str: str) -> str:
        """Санитизация пользовательского ввода"""
        if not input_str:
            return ""
            
        sanitized = re.sub(r'<[^>]*>', '', input_str)
        sanitized = re.sub(r'[;\\\'"`]', '', sanitized)
        return sanitized[:1000]

    def detect_xss(self, input_str: str) -> bool:
        """Обнаружение XSS-уязвимостей во вводе"""
        xss_patterns = [
            r'<script>',
            r'javascript:',
            r'onload\s*=\s*["\']?',
            r'onerror\s*=\s*["\']?',
            r'expression\(',
            r'vbscript:'
        ]
        
        for pattern in xss_patterns:
            if re.search(pattern, input_str, re.IGNORECASE):
                return True
        
        return False

    def detect_sqli(self, input_str: str) -> bool:
        """Обнаружение SQL-инъекций во вводе"""
        sqli_patterns = [
            r'\bUNION\s+SELECT\b',
            r'\bSELECT\s.*\bFROM\b',
            r'\bINSERT\s+INTO\b',
            r'\bUPDATE\s.*\bSET\b',
            r'\bDELETE\s+FROM\b',
            r'\bDROP\s+TABLE\b',
            r'\bOR\s+1\s*=\s*1\b',
            r'\bEXEC\s*\(@',
            r'\bWAITFOR\s+DELAY\b'
        ]
        
        for pattern in sqli_patterns:
            if re.search(pattern, input_str, re.IGNORECASE):
                return True
        
        return False

    def log_security_event(self, event_type: str, details: str, severity: str = "medium", user_id: Optional[int] = None):
        """Логирование события безопасности"""
        truncated_details = details[:500] + "..." if len(details) > 500 else details
        
        event = {
            'timestamp': datetime.now().isoformat(),
            'event_type': event_type,
            'severity': severity,
            'user_id': user_id,
            'details': truncated_details,
            'ip': None
        }
        
        self.security_events.append(event)
        logging.info(f"Событие безопасности: {event_type} - {truncated_details}")
        
        if severity in ["high", "critical"]:
            self.alert_admins(f"🚨 Security alert: {event_type} - {truncated_details}")

    def alert_admins(self, message: str):
        """Оповещение администраторов о критических событиях"""
        logging.critical(f"SECURITY ALERT: {message}")

    def check_password_strength(self, password: str) -> dict:
        """Комплексная проверка сложности пароля"""
        result = {
            'length': len(password),
            'strength': 0,
            'entropy': 0,
            'issues': []
        }
        
        if len(password) < self.password_policy['min_length']:
            result['issues'].append(
                f"Слишком короткий (минимум {self.password_policy['min_length']} символов)"
            )
        elif len(password) > self.password_policy['max_length']:
            result['issues'].append(
                f"Слишком длинный (максимум {self.password_policy['max_length']} символов)"
            )
        
        has_upper = bool(re.search(r'[A-Z]', password))
        has_lower = bool(re.search(r'[a-z]', password))
        has_digit = bool(re.search(r'\d', password))
        has_special = bool(re.search(r'[^A-Za-z0-9]', password))
        
        if not has_upper and self.password_policy['require_upper']:
            result['issues'].append("Нет заглавных букв")
        if not has_lower and self.password_policy['require_lower']:
            result['issues'].append("Нет строчных букв")
        if not has_digit and self.password_policy['require_digit']:
            result['issues'].append("Нет цифр")
        if not has_special and self.password_policy['require_special']:
            result['issues'].append("Нет специальных символов")
        
        char_set = 0
        if has_upper:
            char_set += 26
        if has_lower:
            char_set += 26
        if has_digit:
            char_set += 10
        if has_special:
            char_set += 32
        
        if char_set > 0:
            result['entropy'] = len(password) * math.log2(char_set)
        
        if result['entropy'] < 30:
            result['strength'] = 1
        elif result['entropy'] < 50:
            result['strength'] = 2
        elif result['entropy'] < 70:
            result['strength'] = 3
        elif result['entropy'] < 100:
            result['strength'] = 4
        else:
            result['strength'] = 5
        
        if password.lower() in self.common_passwords:
            result['strength'] = 1
            result['issues'].append("Пароль слишком распространен")
        
        if re.search(r'(.)\1{2,}', password):
            result['issues'].append("Слишком много повторяющихся символов")
        
        if re.search(r'123|234|345|456|567|678|789|890', password):
            result['issues'].append("Обнаружена числовая последовательность")
        if re.search(r'qwer|wert|erty|rtyu|tyui|yuio|uiop', password.lower()):
            result['issues'].append("Обнаружена последовательность букв")
        
        return result
    """Комплексная система безопасности для защиты приложения"""
    
    def __init__(self, config: Config):
        self.config = config
        self.rate_limits = {}  # Счетчики ограничения скорости
        self.lockout_tracker = {}  # Трекер блокировок
        self._init_crypto()
        
        # Политика паролей с улучшенными параметрами
        self.password_policy = {
            'min_length': max(12, config.PASSWORD_MIN_LENGTH),
            'max_length': 128,
            'require_upper': True,
            'require_lower': True,
            'require_digit': True,
            'require_special': True,
            'block_common': True,
            'block_repeats': True,
            'block_sequences': True
        }
        
        # Ленивая загрузка списка распространенных паролей
        self._common_passwords = None
        
        # Инициализация систем мониторинга
        self._init_monitoring()
        logging.info("Система безопасности инициализирована")

    def _init_crypto(self):
        """Инициализация криптографических компонентов"""
        # Настройка Argon2 для хеширования паролей с улучшенными параметрами
        self.password_hasher = argon2.PasswordHasher(
            time_cost=3,          # Увеличенное время вычисления
            memory_cost=65536,    # 64MB памяти
            parallelism=4,        # 4 потока
            hash_len=32,          # Длина хеша 32 байта
            salt_len=16           # Длина соли 16 байт
        )
        
        # Инициализация Fernet для симметричного шифрования
        try:
            self.cipher_suite = Fernet(self.config.FERNET_KEY.encode())
        except Exception as e:
            logging.critical(f"Ошибка инициализации шифрования: {e}")
            raise SecurityException("Ошибка инициализации системы шифрования")
        
        # Генератор криптографически безопасных случайных чисел
        self.rng = secrets.SystemRandom()
    
    @property
    def common_passwords(self) -> set:
        """Ленивая загрузка списка распространенных паролей"""
        if self._common_passwords is None:
            self._common_passwords = self._load_common_passwords()
        return self._common_passwords
    
    def _load_common_passwords(self) -> set:
        """Загрузка списка распространенных паролей из файла"""
        try:
            security_dir = Path('security')
            security_dir.mkdir(parents=True, exist_ok=True)
            common_passwords_path = security_dir / 'common_passwords.txt'
            
            # Создание файла с паролями по умолчанию если не существует
            if not common_passwords_path.exists():
                default_passwords = self._get_default_common_passwords()
                with open(common_passwords_path, 'w', encoding='utf-8') as f:
                    f.write("\n".join(default_passwords))
                logging.info("Создан файл common_passwords.txt с базовыми паролями")
                return set(default_passwords)
            
            # Чтение паролей из файла
            with open(common_passwords_path, 'r', encoding='utf-8') as f:
                passwords = {line.strip().lower() for line in f if line.strip()}
                
                if not passwords:
                    logging.warning("Файл common_passwords.txt пуст, используется базовый набор")
                    return self._get_default_common_passwords()
                    
                return passwords
        except Exception as e:
            logging.error(f"Ошибка загрузки списка паролей: {e}")
            return self._get_default_common_passwords()
    
    def _get_default_common_passwords(self) -> set:
        """Возвращает базовый набор распространенных паролей"""
        return {
            'password', '123456', 'qwerty', 'admin', 'welcome',
            '12345678', '111111', 'sunshine', 'iloveyou', 'password1',
            'admin123', 'letmein', 'monkey', 'football', '123123',
            '123456789', '1234567890', '12345', '1234', '1234567',
            'dragon', 'baseball', 'abc123', 'superman', 'master',
            'trustno1', 'access', 'flower', 'hello', 'solo',
            'secret', 'mustang', 'michael', 'shadow', 'jennifer',
            'jordan', '1111', 'asdfgh', '123qwe', 'qwerty123',
            '1q2w3e4r', 'qwertyuiop', 'passw0rd', 'starwars', 'freedom'
        }
    
    def _init_monitoring(self):
        """Инициализация систем мониторинга безопасности"""
        self.security_events = []  # Хранение событий безопасности
        self.anomaly_detector = AnomalyDetector()  # Детектор аномалий
        
        # Инициализация планировщика для фоновых задач безопасности
        self.scheduler = BackgroundScheduler()
        self.scheduler.add_job(
            self._check_security_status,
            'interval',
            minutes=30,
            next_run_time=datetime.now() + timedelta(minutes=5)
        )
        self.scheduler.start()
        logging.info("Мониторинг безопасности активирован")

    def _check_security_status(self):
        """Периодическая проверка состояния безопасности"""
        try:
            logging.info("Запуск проверки состояния безопасности...")
            
            # Сбор текущей статистики безопасности
            current_stats = {
                'login_attempts': random.randint(0, 10),  # Заглушка, в реальности собираем статистику
                'password_errors': random.randint(0, 5),
                'mfa_failures': random.randint(0, 3),
                'payment_attempts': random.randint(0, 7)
            }
            
            # Проверка на аномалии
            if self.anomaly_detector.detect_anomalies(current_stats):
                alert_msg = "Обнаружена подозрительная активность в системе безопасности!"
                logging.warning(alert_msg)
                self.alert_admins(f"⚠️ {alert_msg}")
            
            # Очистка устаревших данных
            self._cleanup_expired_lockouts()
            self._rotate_security_logs()
            
            logging.info("Проверка безопасности завершена")
        except Exception as e:
            logging.error(f"Ошибка проверки безопасности: {e}")

    def _cleanup_expired_lockouts(self):
        """Очистка устаревших записей о блокировках"""
        now = time.time()
        expired_keys = [
            key for key, timestamp in self.lockout_tracker.items()
            if now - timestamp > self.config.LOCKOUT_TIME
        ]
        
        for key in expired_keys:
            del self.lockout_tracker[key]
        
        if expired_keys:
            logging.info(f"Очищено {len(expired_keys)} устаревших блокировок")

    def _rotate_security_logs(self):
        """Ротация логов безопасности при достижении лимита"""
        if len(self.security_events) > 1000:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            logs_dir = Path('security/logs')
            logs_dir.mkdir(parents=True, exist_ok=True)
            filename = logs_dir / f"security_events_{timestamp}.log"
            
            try:
                with open(filename, 'w', encoding='utf-8') as f:
                    for event in self.security_events:
                        f.write(json.dumps(event, ensure_ascii=False) + "\n")
                
                self.security_events.clear()
                logging.info(f"Логи безопасности сохранены в {filename}")
            except Exception as e:
                logging.error(f"Ошибка ротации логов безопасности: {e}")

    def hash_password(self, password: str) -> str:
        """
        Хеширование пароля с проверкой политики безопасности
        Возвращает хеш пароля или вызывает SecurityException
        """
        # Предварительная валидация пароля
        self._validate_password_policy(password)
        
        # Создание хеша с использованием Argon2
        try:
            return self.password_hasher.hash(password)
        except argon2.exceptions.HashingError as e:
            logging.error(f"Ошибка хеширования пароля: {e}")
            raise SecurityException("Ошибка создания хеша пароля")
    
    def _validate_password_policy(self, password: str):
        """Проверка соответствия пароля политике безопасности"""
        if not isinstance(password, str):
            raise SecurityException("Пароль должен быть строкой")
        
        # Проверка длины
        if len(password) < self.password_policy['min_length']:
            raise SecurityException(
                f"Пароль должен содержать не менее {self.password_policy['min_length']} символов"
            )
        
        if len(password) > self.password_policy['max_length']:
            raise SecurityException(
                f"Пароль должен содержать не более {self.password_policy['max_length']} символов"
            )
        
        # Проверка сложности
        if self.password_policy['require_upper'] and not re.search(r'[A-Z]', password):
            raise SecurityException("Пароль должен содержать заглавные буквы")
        
        if self.password_policy['require_lower'] and not re.search(r'[a-z]', password):
            raise SecurityException("Пароль должен содержать строчные буквы")
        
        if self.password_policy['require_digit'] and not re.search(r'\d', password):
            raise SecurityException("Пароль должен содержать цифры")
        
        if self.password_policy['require_special'] and not re.search(r'[!@#$%^&*(),.?":{}|<>]', password):
            raise SecurityException("Пароль должен содержать специальные символы")
        
        # Проверка на распространенные пароли
        if self.password_policy['block_common'] and password.lower() in self.common_passwords:
            raise SecurityException("Пароль слишком распространен и ненадежен")
        
        # Проверка на повторяющиеся символы
        if self.password_policy['block_repeats'] and re.search(r'(.)\1{2,}', password):
            raise SecurityException("Пароль содержит повторяющиеся символы")
        
        # Проверка на простые последовательности
        if self.password_policy['block_sequences'] and (
            re.search(r'123|234|345|456|567|678|789|890', password) or
            re.search(r'qwer|wert|erty|rtyu|tyui|yuio|uiop', password.lower())
        ):
            raise SecurityException("Пароль содержит простые последовательности символов")

    def verify_password(self, password: str, stored_hash: str) -> bool:
        """
        Проверка соответствия пароля хранимому хешу
        Возвращает True если пароль верный, False если нет
        """
        if not password or not stored_hash:
            return False
        
        start_time = time.monotonic()
        
        try:
            # Верификация пароля
            result = self.password_hasher.verify(stored_hash, password)
            
            # Проверка необходимости перехеширования
            if result and self.password_hasher.check_needs_rehash(stored_hash):
                self.log_security_event(
                    "password_rehash_needed",
                    "Password hash needs rehashing",
                    severity="medium"
                )
            
            return result
        except argon2.exceptions.VerifyMismatchError:
            # Фиксация времени проверки для выявления брутфорса
            elapsed = time.monotonic() - start_time
            self._detect_bruteforce_attempt(elapsed)
            return False
        except argon2.exceptions.InvalidHash as e:
            self.log_security_event(
                "invalid_hash_format",
                f"Invalid hash format during verification: {str(e)}",
                severity="high"
            )
            return False
        except Exception as e:
            self.log_security_event(
                "password_verification_error",
                f"Unexpected error: {str(e)}",
                severity="critical"
            )
            return False
    
    def _detect_bruteforce_attempt(self, verification_time: float):
        """
        Обнаружение возможной атаки перебора по времени верификации
        Слишком быстрое или слишком медленное время может указывать на атаку
        """
        if verification_time < 0.1:  # Слишком быстро для Argon2
            self.log_security_event(
                "suspicious_verification_speed",
                f"Password verification too fast: {verification_time:.6f}s",
                severity="high"
            )
        
        if verification_time > 1.0:  # Слишком медленно для нормальной работы
            self.log_security_event(
                "suspicious_verification_speed",
                f"Password verification too slow: {verification_time:.6f}s",
                severity="high"
            )

    def generate_mfa_secret(self) -> str:
        """Генерация секретного ключа для двухфакторной аутентификации"""
        return pyotp.random_base32()

    def generate_mfa_qr(self, secret: str, username: str) -> BytesIO:
        """Генерация QR-кода для настройки двухфакторной аутентификации"""
        try:
            # Форматирование имени приложения для URI
            issuer_name = re.sub(r'\s+', '', self.config.APP_NAME)
            
            # Генерация URI для приложения аутентификатора
            uri = pyotp.totp.TOTP(secret).provisioning_uri(
                name=username,
                issuer_name=issuer_name
            )
            
            # Создание QR-кода
            qr = qrcode.QRCode(
                version=1,
                error_correction=qrcode.constants.ERROR_CORRECT_L,
                box_size=10,
                border=4,
            )
            qr.add_data(uri)
            qr.make(fit=True)
            
            # Сохранение в буфер
            img = qr.make_image(fill_color="black", back_color="white")
            buf = BytesIO()
            img.save(buf, format="PNG")
            buf.seek(0)
            
            return buf
        except Exception as e:
            logging.error(f"Ошибка генерации QR-кода: {e}")
            raise SecurityException("Ошибка генерации QR-кода для 2FA")

    def verify_mfa_code(self, secret: str, code: str, window: int = 1) -> bool:
        """Проверка кода двухфакторной аутентификации"""
        if not secret or not code:
            return False
        
        # Базовая проверка формата кода
        if not re.match(r'^\d{6}$', code):
            return False
        
        try:
            # Верификация кода с использованием TOTP
            return pyotp.TOTP(secret).verify(code, valid_window=window)
        except Exception as e:
            logging.error(f"Ошибка проверки MFA кода: {e}")
            return False

    def encrypt_data(self, data: Union[str, dict]) -> str:
        """Шифрование конфиденциальных данных"""
        try:
            # Преобразование словарей в JSON
            if isinstance(data, dict):
                data = json.dumps(data, ensure_ascii=False)
            
            # Шифрование данных
            encrypted = self.cipher_suite.encrypt(data.encode('utf-8'))
            return base64.urlsafe_b64encode(encrypted).decode('utf-8')
        except Exception as e:
            logging.error(f"Ошибка шифрования данных: {e}")
            raise SecurityException("Ошибка шифрования данных")

    def decrypt_data(self, encrypted_data: str) -> str:
        """Дешифрование данных"""
        try:
            # Декодирование из URL-safe Base64
            encrypted_bytes = base64.urlsafe_b64decode(encrypted_data)
            
            # Дешифрование
            return self.cipher_suite.decrypt(encrypted_bytes).decode('utf-8')
        except InvalidToken:
            self.log_security_event(
                "decryption_failed",
                "Invalid token during decryption",
                severity="high"
            )
            raise SecurityException("Ошибка дешифрования: неверный токен")
        except Exception as e:
            self.log_security_event(
                "decryption_error",
                f"Decryption failed: {str(e)}",
                severity="critical"
            )
            raise SecurityException(f"Ошибка дешифрования: {str(e)}")

    def check_rate_limit(self, identifier: str, action: str, max_attempts: int, period: int) -> bool:
        """
        Проверка ограничения скорости запросов
        Возвращает True если запрос разрешен, False при превышении лимита
        """
        key = f"{identifier}_{action}"
        now = time.time()
        
        # Проверка блокировки
        if key in self.lockout_tracker:
            lockout_time = self.lockout_tracker[key]
            elapsed = now - lockout_time
            if elapsed < period:
                return False
            del self.lockout_tracker[key]
        
        # Инициализация счетчика
        if key not in self.rate_limits:
            self.rate_limits[key] = {
                'count': 1,
                'timestamp': now
            }
            return True
        
        # Сброс счетчика при истечении периода
        if now - self.rate_limits[key]['timestamp'] > period:
            self.rate_limits[key] = {
                'count': 1,
                'timestamp': now
            }
            return True
        
        # Увеличение счетчика
        self.rate_limits[key]['count'] += 1
        
        # Проверка превышения лимита
        if self.rate_limits[key]['count'] > max_attempts:
            self.lockout_tracker[key] = now
            self.log_security_event(
                "rate_limit_exceeded",
                f"Action: {action}, Identifier: {identifier}",
                severity="high"
            )
            return False
        
        return True

    def generate_secure_token(self, length: int = 32) -> str:
        """Генерация криптографически безопасного токена"""
        if length < 16:
            raise ValueError("Длина токена должна быть не менее 16 символов")
        return secrets.token_urlsafe(length)

    def validate_input(self, input_str: str, pattern: str, min_len: int = 1, max_len: int = 255) -> bool:
        """Комплексная валидация пользовательского ввода"""
        # Проверка типа и длины
        if not isinstance(input_str, str):
            return False
        if len(input_str) < min_len or len(input_str) > max_len:
            return False
        
        # Проверка по регулярному выражению
        if not re.fullmatch(pattern, input_str):
            return False
        
        # Проверка на опасные конструкции
        dangerous_patterns = [
            r';', r'--', r'/\*', r'\*/', r'xp_',
            r'<script>', r'</script>', r'javascript:',
            r'onload\s*=', r'onerror\s*=', r'expression\('
        ]
        
        for danger in dangerous_patterns:
            if re.search(danger, input_str, re.IGNORECASE):
                return False
        
        return True

    def validate_steam_login(self, login: str) -> bool:
        """Валидация Steam логина"""
        return self.validate_input(
            login,
            r'^[a-zA-Z][a-zA-Z0-9_]{2,31}$',
            min_len=3,
            max_len=32
        ) and not any(c in login for c in ['@', ' ', '"', "'", ';'])

    async def validate_email(self, email: str) -> bool:
        """Комплексная валидация email адреса"""
        # Проверка формата
        if not re.match(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$', email):
            return False
        
        # Проверка существования домена
        try:
            domain = email.split('@')[1]
            loop = asyncio.get_running_loop()
            
            # DNS проверка домена
            await loop.getaddrinfo(domain, None)
            return True
        except (socket.gaierror, IndexError, ValueError):
            return False
        except Exception as e:
            logging.error(f"Ошибка проверки DNS для email: {e}")
            return False

    def validate_phone(self, phone: str) -> bool:
        """Валидация номера телефона"""
        return re.match(r'^\+?[1-9]\d{1,14}$', phone) is not None

    def validate_wallet_address(self, wallet: str) -> bool:
        """Валидация адреса криптовалютного кошелька"""
        return self.validate_input(
            wallet,
            r'^[a-zA-Z0-9]{20,50}$',
            min_len=MIN_WALLET_ADDRESS_LENGTH,
            max_len=MAX_WALLET_ADDRESS_LENGTH
        )

    def sanitize_input(self, input_str: str) -> str:
        """Санитизация пользовательского ввода"""
        if not input_str:
            return ""
            
        # Удаление HTML тегов
        sanitized = re.sub(r'<[^>]*>', '', input_str)
        
        # Удаление опасных символов
        sanitized = re.sub(r'[;\\\'"`]', '', sanitized)
        
        # Ограничение длины
        return sanitized[:1000]

    def detect_xss(self, input_str: str) -> bool:
        """Обнаружение XSS-уязвимостей во вводе"""
        xss_patterns = [
            r'<script>',
            r'javascript:',
            r'onload\s*=\s*["\']?',
            r'onerror\s*=\s*["\']?',
            r'expression\(',
            r'vbscript:'
        ]
        
        for pattern in xss_patterns:
            if re.search(pattern, input_str, re.IGNORECASE):
                return True
        
        return False

    def detect_sqli(self, input_str: str) -> bool:
        """Обнаружение SQL-инъекций во вводе"""
        sqli_patterns = [
            r'\bUNION\s+SELECT\b',
            r'\bSELECT\s.*\bFROM\b',
            r'\bINSERT\s+INTO\b',
            r'\bUPDATE\s.*\bSET\b',
            r'\bDELETE\s+FROM\b',
            r'\bDROP\s+TABLE\b',
            r'\bOR\s+1\s*=\s*1\b',
            r'\bEXEC\s*\(@',
            r'\bWAITFOR\s+DELAY\b'
        ]
        
        for pattern in sqli_patterns:
            if re.search(pattern, input_str, re.IGNORECASE):
                return True
        
        return False

    def log_security_event(self, event_type: str, details: str, severity: str = "medium", user_id: Optional[int] = None):
        """Логирование события безопасности"""
        truncated_details = details[:500] + "..." if len(details) > 500 else details
        
        event = {
            'timestamp': datetime.now().isoformat(),
            'event_type': event_type,
            'severity': severity,
            'user_id': user_id,
            'details': truncated_details,
            'ip': None
        }
        
        self.security_events.append(event)
        logging.info(f"Событие безопасности: {event_type} - {truncated_details}")
        
        if severity in ["high", "critical"]:
            self.alert_admins(f"🚨 Security alert: {event_type} - {truncated_details}")

    def alert_admins(self, message: str):
        """Оповещение администраторов о критических событиях"""
        logging.critical(f"SECURITY ALERT: {message}")
        # В реальной системе здесь должна быть интеграция с системой оповещений
        # Например, отправка сообщений администраторам через Telegram API

    def check_password_strength(self, password: str) -> dict:
        """Комплексная проверка сложности пароля"""
        result = {
            'length': len(password),
            'strength': 0,         # 1-5 (очень слабый - очень сильный)
            'entropy': 0,          # Энтропия в битах
            'issues': []          # Список проблем
        }
        
        # Проверка длины
        if len(password) < self.password_policy['min_length']:
            result['issues'].append(
                f"Слишком короткий (минимум {self.password_policy['min_length']} символов)"
            )
        elif len(password) > self.password_policy['max_length']:
            result['issues'].append(
                f"Слишком длинный (максимум {self.password_policy['max_length']} символов)"
            )
        
        # Проверка наличия категорий символов
        has_upper = bool(re.search(r'[A-Z]', password))
        has_lower = bool(re.search(r'[a-z]', password))
        has_digit = bool(re.search(r'\d', password))
        has_special = bool(re.search(r'[^A-Za-z0-9]', password))
        
        if not has_upper and self.password_policy['require_upper']:
            result['issues'].append("Нет заглавных букв")
        if not has_lower and self.password_policy['require_lower']:
            result['issues'].append("Нет строчных букв")
        if not has_digit and self.password_policy['require_digit']:
            result['issues'].append("Нет цифр")
        if not has_special and self.password_policy['require_special']:
            result['issues'].append("Нет специальных символов")
        
        # Расчет энтропии
        char_set = 0
        if has_upper:
            char_set += 26
        if has_lower:
            char_set += 26
        if has_digit:
            char_set += 10
        if has_special:
            char_set += 32  # Приблизительное количество спецсимволов
        
        if char_set > 0:
            result['entropy'] = len(password) * math.log2(char_set)
        else:
            result['entropy'] = 0
        
        # Определение уровня сложности на основе энтропии
        if result['entropy'] < 30:
            result['strength'] = 1
        elif result['entropy'] < 50:
            result['strength'] = 2
        elif result['entropy'] < 70:
            result['strength'] = 3
        elif result['entropy'] < 100:
            result['strength'] = 4
        else:
            result['strength'] = 5
        
        # Проверка на распространенные пароли
        if password.lower() in self.common_passwords:
            result['strength'] = 1
            result['issues'].append("Пароль слишком распространен")
        
        # Проверка на повторяющиеся символы
        if re.search(r'(.)\1{2,}', password):
            result['issues'].append("Слишком много повторяющихся символов")
        
        # Проверка на последовательности
        if re.search(r'123|234|345|456|567|678|789|890', password):
            result['issues'].append("Обнаружена числовая последовательность")
        if re.search(r'qwer|wert|erty|rtyu|tyui|yuio|uiop', password.lower()):
            result['issues'].append("Обнаружена последовательность букв")
        
        return result
    
class AdminPanel:
    """Панель администратора для управления системой"""
    
    def __init__(self, db: Database, security: Security):
        self.db = db
        self.security = security
        self.config = security.config
        logging.info("Админ-панель инициализирована")

    async def is_admin(self, user_id: int) -> bool:
        """Проверка, является ли пользователь администратором"""
        return user_id in self.config.ADMIN_IDS
    
    async def get_system_stats(self) -> dict:
        """Получение базовой статистики системы"""
        stats = {
            "users": 0,
            "active_users": 0,
            "new_users_24h": 0,
            "transactions": 0,
            "completed_transactions": 0,
            "total_volume": Decimal('0'),
            "tickets": 0,
            "open_tickets": 0
        }
        
        try:
            # Статистика пользователей
            users_stats = await self.db.fetch_one(
                """SELECT 
                    COUNT(*) as total_users,
                    SUM(CASE WHEN created_at > datetime('now', '-1 day') THEN 1 ELSE 0 END) as new_users,
                    SUM(CASE WHEN last_login > datetime('now', '-7 day') THEN 1 ELSE 0 END) as active_users
                FROM users"""
            )
            
            if users_stats:
                stats.update({
                    "users": users_stats['total_users'],
                    "active_users": users_stats['active_users'],
                    "new_users_24h": users_stats['new_users']
                })

            # Статистика транзакций
            transactions_stats = await self.db.fetch_one(
                """SELECT 
                    COUNT(*) as total_transactions,
                    SUM(CASE WHEN status = 'completed' THEN 1 ELSE 0 END) as completed_transactions,
                    SUM(CASE WHEN status = 'completed' THEN amount ELSE 0 END) as total_volume
                FROM transactions"""
            )
            
            if transactions_stats:
                stats.update({
                    "transactions": transactions_stats['total_transactions'],
                    "completed_transactions": transactions_stats['completed_transactions'],
                    "total_volume": Decimal(transactions_stats['total_volume'] or '0')
                })

            # Статистика тикетов
            tickets_stats = await self.db.fetch_one(
                """SELECT 
                    COUNT(*) as total_tickets,
                    SUM(CASE WHEN status = 'open' THEN 1 ELSE 0 END) as open_tickets
                FROM support_tickets"""
            )
            
            if tickets_stats:
                stats.update({
                    "tickets": tickets_stats['total_tickets'],
                    "open_tickets": tickets_stats['open_tickets']
                })

        except Exception as e:
            logging.error(f"Ошибка получения статистики: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения статистики")
        
        return stats

    async def get_detailed_stats(self, period_days: int = 7) -> dict:
        """Получение детальной статистики за указанный период"""
        stats = await self.get_system_stats()
        
        try:
            # Детальная статистика пользователей
            stats['user_growth'] = await self._get_user_growth_stats(period_days)
            
            # Статистика транзакций по дням
            stats['transactions_by_day'] = await self._get_transactions_by_day(period_days)
            
            # Статистика по типам транзакций
            stats['transactions_by_type'] = await self._get_transactions_by_type(period_days)
            
            # Распределение платежей
            stats['payment_distribution'] = await self._get_payment_distribution()

        except Exception as e:
            logging.error(f"Ошибка получения детальной статистики: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения детальной статистики")
        
        return stats

    async def _get_user_growth_stats(self, period_days: int) -> List[dict]:
        """Получение статистики роста пользователей"""
        return await self.db.fetch_all(
            """SELECT 
                date(created_at) as date,
                COUNT(*) as new_users,
                SUM(COUNT(*)) OVER (ORDER BY date(created_at)) as total_users
            FROM users
            WHERE created_at > datetime('now', ?)
            GROUP BY date(created_at)
            ORDER BY date""",
            (f"-{period_days} days",)
        )

    async def _get_transactions_by_day(self, period_days: int) -> List[dict]:
        """Получение статистики транзакций по дням"""
        return await self.db.fetch_all(
            """SELECT 
                date(created_at) as date,
                COUNT(*) as count,
                SUM(amount) as volume
            FROM transactions
            WHERE created_at > datetime('now', ?)
            GROUP BY date(created_at)
            ORDER BY date""",
            (f"-{period_days} days",)
        )

    async def _get_transactions_by_type(self, period_days: int) -> List[dict]:
        """Получение статистики транзакций по типам"""
        return await self.db.fetch_all(
            """SELECT 
                type,
                COUNT(*) as count,
                SUM(amount) as volume
            FROM transactions
            WHERE created_at > datetime('now', ?)
            GROUP BY type
            ORDER BY volume DESC""",
            (f"-{period_days} days",)
        )

    async def _get_payment_distribution(self) -> List[dict]:
        """Получение распределения платежей по суммам"""
        return await self.db.fetch_all(
            """SELECT 
                CASE
                    WHEN amount < 100 THEN '0-100'
                    WHEN amount < 500 THEN '100-500'
                    WHEN amount < 1000 THEN '500-1000'
                    WHEN amount < 5000 THEN '1000-5000'
                    ELSE '5000+'
                END as range,
                COUNT(*) as count,
                SUM(amount) as volume
            FROM transactions
            WHERE status = 'completed' AND type = 'deposit'
            GROUP BY range
            ORDER BY volume DESC"""
        )

    async def get_user_list(self, page: int = 1, per_page: int = 20) -> dict:
        """Получение списка пользователей с пагинацией"""
        offset = (page - 1) * per_page
        
        try:
            users = await self.db.fetch_all(
                """SELECT 
                    user_id, 
                    username, 
                    balance, 
                    is_active,
                    date(created_at) as reg_date,
                    date(last_login) as last_login
                FROM users
                ORDER BY created_at DESC
                LIMIT ? OFFSET ?""",
                (per_page, offset)
            )
            
            total = await self.db.fetch_one("SELECT COUNT(*) as count FROM users")
            
            return {
                "users": users,
                "total": total['count'] if total else 0,
                "page": page,
                "per_page": per_page,
                "total_pages": (total['count'] + per_page - 1) // per_page if total else 1
            }
        except Exception as e:
            logging.error(f"Ошибка получения списка пользователей: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения списка пользователей")

    async def search_users(self, query: str, limit: int = 20) -> List[dict]:
        """Поиск пользователей по ID, имени или Steam логину"""
        try:
            if query.isdigit():
                # Поиск по ID
                return await self.db.fetch_all(
                    """SELECT 
                        user_id, 
                        username, 
                        balance, 
                        is_active
                    FROM users
                    WHERE user_id = ?
                    LIMIT ?""",
                    (int(query), limit)
                )
            else:
                # Поиск по имени или Steam логину
                search_pattern = f"%{query}%"
                return await self.db.fetch_all(
                    """SELECT 
                        user_id, 
                        username, 
                        balance, 
                        is_active
                    FROM users
                    WHERE username LIKE ? 
                    LIMIT ?""",
                    (search_pattern, limit)
                )
        except Exception as e:
            logging.error(f"Ошибка поиска пользователей: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка поиска пользователей")

    async def get_user_details(self, user_id: int) -> dict:
        """Получение детальной информации о пользователе"""
        try:
            user = await self.db.fetch_one(
                """SELECT 
                    user_id,
                    username,
                    email,
                    phone,
                    balance,
                    is_active,
                    created_at,
                    last_login,
                    failed_login_attempts,
                    mfa_secret IS NOT NULL as has_mfa
                FROM users
                WHERE user_id = ?""",
                (user_id,)
            )
            
            if not user:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Пользователь не найден")
            
            # Получаем последние транзакции пользователя
            transactions = await self.db.fetch_all(
                """SELECT 
                    transaction_id,
                    amount,
                    currency,
                    status,
                    type,
                    date(created_at) as date
                FROM transactions
                WHERE user_id = ?
                ORDER BY created_at DESC
                LIMIT 10""",
                (user_id,)
            )
            
            # Получаем открытые тикеты пользователя
            tickets = await self.db.fetch_all(
                """SELECT 
                    ticket_id,
                    text,
                    status,
                    created_at
                FROM support_tickets
                WHERE user_id = ? AND status = 'open'
                ORDER BY created_at DESC""",
                (user_id,)
            )
            
            return {
                **dict(user),
                "transactions": transactions,
                "tickets": tickets
            }
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка получения данных пользователя: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения данных пользователя")

    async def update_user_status(self, user_id: int, is_active: bool) -> bool:
        """Обновление статуса пользователя (активен/заблокирован)"""
        try:
            await self.db.execute(
                "UPDATE users SET is_active = ? WHERE user_id = ?",
                (int(is_active), user_id),
                commit=True
            )
            
            await self.db.log_audit(
                None,  # Системное действие
                "user_status_change",
                f"User {user_id} status changed to {'active' if is_active else 'inactive'}"
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка обновления статуса пользователя: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка обновления статуса пользователя")

    async def adjust_user_balance(self, user_id: int, amount: Decimal, description: str) -> dict:
        """Изменение баланса пользователя администратором"""
        if abs(amount) > self.config.MAX_MANUAL_BALANCE_CHANGE:
            raise BotError(
                ErrorCode.INVALID_AMOUNT,
                f"Сумма изменения не должна превышать {self.config.MAX_MANUAL_BALANCE_CHANGE}"
            )
        
        try:
            async with self.db.transaction() as tx:
                # Получаем текущий баланс
                user = await tx.execute_fetchone(
                    "SELECT balance FROM users WHERE user_id = ?",
                    (user_id,)
                )
                
                if not user:
                    raise BotError(ErrorCode.USER_NOT_FOUND, "Пользователь не найден")
                
                current_balance = Decimal(user['balance'])
                new_balance = current_balance + amount
                
                if new_balance < 0:
                    raise BotError(
                        ErrorCode.INVALID_AMOUNT,
                        "Итоговый баланс не может быть отрицательным"
                    )
                
                # Обновляем баланс
                await tx.execute(
                    "UPDATE users SET balance = ? WHERE user_id = ?",
                    (float(new_balance), user_id)
                )
                
                # Создаем запись о транзакции
                transaction_id = f"adm_{secrets.token_hex(8)}"
                await tx.execute(
                    """INSERT INTO transactions (
                        transaction_id, user_id, amount, status, type, description
                    ) VALUES (?, ?, ?, ?, ?, ?)""",
                    (
                        transaction_id,
                        user_id,
                        float(amount),
                        'completed',
                        'admin_adjustment',
                        description
                    )
                )
                
                await self.db.log_audit(
                    None,  # Системное действие
                    "balance_adjustment",
                    f"User {user_id} balance changed by {amount} (new balance: {new_balance})"
                )
                
                return {
                    "transaction_id": transaction_id,
                    "user_id": user_id,
                    "amount": amount,
                    "new_balance": new_balance,
                    "previous_balance": current_balance
                }
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка изменения баланса пользователя: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка изменения баланса пользователя")

    async def get_transaction_list(self, page: int = 1, per_page: int = 20, filters: dict = None) -> dict:
        """Получение списка транзакций с пагинацией и фильтрами"""
        filters = filters or {}
        offset = (page - 1) * per_page
        
        try:
            where_clauses = []
            params = []
            
            # Применяем фильтры
            if filters.get('user_id'):
                where_clauses.append("user_id = ?")
                params.append(filters['user_id'])
                
            if filters.get('type'):
                where_clauses.append("type = ?")
                params.append(filters['type'])
                
            if filters.get('status'):
                where_clauses.append("status = ?")
                params.append(filters['status'])
                
            if filters.get('date_from'):
                where_clauses.append("created_at >= ?")
                params.append(filters['date_from'])
                
            if filters.get('date_to'):
                where_clauses.append("created_at <= ?")
                params.append(filters['date_to'])
            
            where = "WHERE " + " AND ".join(where_clauses) if where_clauses else ""
            
            # Получаем транзакции
            transactions = await self.db.fetch_all(
                f"""SELECT 
                    transaction_id,
                    user_id,
                    amount,
                    currency,
                    status,
                    type,
                    wallet_address,
                    date(created_at) as date,
                    description
                FROM transactions
                {where}
                ORDER BY created_at DESC
                LIMIT ? OFFSET ?""",
                (*params, per_page, offset)
            )
            
            # Получаем общее количество
            total = await self.db.fetch_one(
                f"SELECT COUNT(*) as count FROM transactions {where}",
                tuple(params)
            )
            
            return {
                "transactions": transactions,
                "total": total['count'] if total else 0,
                "page": page,
                "per_page": per_page,
                "total_pages": (total['count'] + per_page - 1) // per_page if total else 1
            }
        except Exception as e:
            logging.error(f"Ошибка получения списка транзакций: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения списка транзакций")

    async def get_transaction_details(self, transaction_id: str) -> dict:
        """Получение детальной информации о транзакции"""
        try:
            transaction = await self.db.fetch_one(
                """SELECT 
                    t.transaction_id,
                    t.user_id,
                    u.username,
                    t.amount,
                    t.currency,
                    t.status,
                    t.type,
                    t.wallet_address,
                    t.created_at,
                    t.completed_at,
                    t.description
                FROM transactions t
                LEFT JOIN users u ON t.user_id = u.user_id
                WHERE t.transaction_id = ?""",
                (transaction_id,)
            )
            
            if not transaction:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Транзакция не найдена")
            
            return transaction
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка получения данных транзакции: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения данных транзакции")

    async def update_transaction_status(self, transaction_id: str, status: str) -> bool:
        """Обновление статуса транзакции администратором"""
        valid_statuses = ['pending', 'processing', 'completed', 'failed', 'canceled']
        
        if status not in valid_statuses:
            raise BotError(ErrorCode.INVALID_INPUT, f"Недопустимый статус: {status}")
        
        try:
            await self.db.execute(
                """UPDATE transactions 
                SET status = ?, 
                    completed_at = CASE WHEN ? = 'completed' THEN datetime('now') ELSE completed_at END
                WHERE transaction_id = ?""",
                (status, status, transaction_id),
                commit=True
            )
            
            await self.db.log_audit(
                None,  # Системное действие
                "transaction_status_change",
                f"Transaction {transaction_id} status changed to {status}"
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка обновления статуса транзакции: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка обновления статуса транзакции")

    async def get_ticket_list(self, page: int = 1, per_page: int = 20, status: str = None) -> dict:
        """Получение списка тикетов с пагинацией"""
        offset = (page - 1) * per_page
        
        try:
            where = "WHERE status = ?" if status else ""
            params = (status,) if status else ()
            
            tickets = await self.db.fetch_all(
                f"""SELECT 
                    ticket_id,
                    user_id,
                    username,
                    status,
                    created_at,
                    substr(text, 1, 100) as preview
                FROM support_tickets
                {where}
                ORDER BY created_at DESC
                LIMIT ? OFFSET ?""",
                (*params, per_page, offset)
            )
            
            total = await self.db.fetch_one(
                f"SELECT COUNT(*) as count FROM support_tickets {where}",
                params
            )
            
            return {
                "tickets": tickets,
                "total": total['count'] if total else 0,
                "page": page,
                "per_page": per_page,
                "total_pages": (total['count'] + per_page - 1) // per_page if total else 1
            }
        except Exception as e:
            logging.error(f"Ошибка получения списка тикетов: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения списка тикетов")

    async def get_ticket_details(self, ticket_id: str) -> dict:
        """Получение детальной информации о тикете"""
        try:
            ticket = await self.db.fetch_one(
                """SELECT 
                    ticket_id,
                    user_id,
                    username,
                    text,
                    status,
                    created_at
                FROM support_tickets
                WHERE ticket_id = ?""",
                (ticket_id,)
            )
            
            if not ticket:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Тикет не найден")
            
            return ticket
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка получения данных тикета: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения данных тикета")

    async def update_ticket_status(self, ticket_id: str, status: str) -> bool:
        """Обновление статуса тикета"""
        valid_statuses = ['open', 'closed', 'pending', 'resolved']
        
        if status not in valid_statuses:
            raise BotError(ErrorCode.INVALID_INPUT, f"Недопустимый статус: {status}")
        
        try:
            await self.db.execute(
                "UPDATE support_tickets SET status = ? WHERE ticket_id = ?",
                (status, ticket_id),
                commit=True
            )
            
            await self.db.log_audit(
                None,  # Системное действие
                "ticket_status_change",
                f"Ticket {ticket_id} status changed to {status}"
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка обновления статуса тикета: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка обновления статуса тикета")

    async def add_ticket_comment(self, ticket_id: str, admin_id: int, comment: str) -> bool:
        """Добавление комментария администратора к тикету"""
        try:
            # Сохраняем комментарий в базе данных
            await self.db.execute(
                """UPDATE support_tickets 
                SET text = text || '\n\n[ADMIN]: ' || ?
                WHERE ticket_id = ?""",
                (comment, ticket_id),
                commit=True
            )
            
            await self.db.log_audit(
                admin_id,
                "ticket_comment_added",
                f"Comment added to ticket {ticket_id}"
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка добавления комментария к тикету: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка добавления комментария к тикету")

    async def notify_user(self, user_id: int, message: str) -> bool:
        """Отправка уведомления пользователю от имени администратора"""
        try:
            # В реальной системе здесь будет отправка сообщения через Telegram API
            logging.info(f"Уведомление для пользователя {user_id}: {message}")
            
            await self.db.log_audit(
                None,  # Системное действие
                "admin_notification",
                f"User {user_id} notified with message: {message[:100]}..."
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка отправки уведомления: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка отправки уведомления")

    async def get_audit_log(self, page: int = 1, per_page: int = 20, filters: dict = None) -> dict:
        """Получение лога аудита с пагинацией"""
        filters = filters or {}
        offset = (page - 1) * per_page
        
        try:
            where_clauses = []
            params = []
            
            # Применяем фильтры
            if filters.get('user_id'):
                where_clauses.append("user_id = ?")
                params.append(filters['user_id'])
                
            if filters.get('action_type'):
                where_clauses.append("action_type = ?")
                params.append(filters['action_type'])
                
            if filters.get('date_from'):
                where_clauses.append("created_at >= ?")
                params.append(filters['date_from'])
                
            if filters.get('date_to'):
                where_clauses.append("created_at <= ?")
                params.append(filters['date_to'])
            
            where = "WHERE " + " AND ".join(where_clauses) if where_clauses else ""
            
            # Получаем записи
            logs = await self.db.fetch_all(
                f"""SELECT 
                    log_id,
                    user_id,
                    action_type,
                    substr(action_details, 1, 100) as action_preview,
                    ip_address,
                    created_at
                FROM audit_log
                {where}
                ORDER BY created_at DESC
                LIMIT ? OFFSET ?""",
                (*params, per_page, offset)
            )
            
            # Получаем общее количество
            total = await self.db.fetch_one(
                f"SELECT COUNT(*) as count FROM audit_log {where}",
                tuple(params)
            )
            
            return {
                "logs": logs,
                "total": total['count'] if total else 0,
                "page": page,
                "per_page": per_page,
                "total_pages": (total['count'] + per_page - 1) // per_page if total else 1
            }
        except Exception as e:
            logging.error(f"Ошибка получения лога аудита: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения лога аудита")

    async def get_audit_log_details(self, log_id: int) -> dict:
        """Получение детальной информации о записи аудита"""
        try:
            log = await self.db.fetch_one(
                """SELECT 
                    log_id,
                    user_id,
                    action_type,
                    action_details,
                    ip_address,
                    user_agent,
                    created_at
                FROM audit_log
                WHERE log_id = ?""",
                (log_id,)
            )
            
            if not log:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Запись аудита не найден")
            
            return log
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка получения данных аудита: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения данных аудита")

    async def create_backup(self) -> str:
        """Создание резервной копии базы данных"""
        try:
            if await self.db.backup():
                return "Резервная копия успешно создана"
            else:
                raise BotError(ErrorCode.DATABASE_ERROR, "Не удалось создать резервную копию")
        except Exception as e:
            logging.error(f"Ошибка создания резервной копии: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка создания резервной копии")

    async def notify_admins(self, message: str, exclude_admin_id: int = None):
        """Уведомление всех администраторов"""
        if not self.config.ADMIN_IDS:
            return
            
        for admin_id in self.config.ADMIN_IDS:
            if admin_id == exclude_admin_id:
                continue
                
            try:
                # В реальной системе здесь будет отправка сообщения через Telegram API
                logging.info(f"Уведомление администратора {admin_id}: {message}")
            except Exception as e:
                logging.error(f"Не удалось уведомить администратора {admin_id}: {e}")
    """Панель администратора для управления системой"""
    
    def __init__(self, db: Database, security: Security):
        self.db = db
        self.security = security
        self.config = security.config
        logging.info("Админ-панель инициализирована")

    async def is_admin(self, user_id: int) -> bool:
        """Проверка, является ли пользователь администратором"""
        return user_id in self.config.ADMIN_IDS
    
    async def get_system_stats(self) -> dict:
        """Получение базовой статистики системы"""
        stats = {
            "users": 0,
            "active_users": 0,
            "new_users_24h": 0,
            "transactions": 0,
            "completed_transactions": 0,
            "total_volume": Decimal('0'),
            "tickets": 0,
            "open_tickets": 0
        }
        
        try:
            # Статистика пользователей
            users_stats = await self.db.fetch_one(
                """SELECT 
                    COUNT(*) as total_users,
                    SUM(CASE WHEN created_at > datetime('now', '-1 day') THEN 1 ELSE 0 END) as new_users,
                    SUM(CASE WHEN last_login > datetime('now', '-7 day') THEN 1 ELSE 0 END) as active_users
                FROM users"""
            )
            
            if users_stats:
                stats.update({
                    "users": users_stats['total_users'],
                    "active_users": users_stats['active_users'],
                    "new_users_24h": users_stats['new_users']
                })

            # Статистика транзакций
            transactions_stats = await self.db.fetch_one(
                """SELECT 
                    COUNT(*) as total_transactions,
                    SUM(CASE WHEN status = 'completed' THEN 1 ELSE 0 END) as completed_transactions,
                    SUM(CASE WHEN status = 'completed' THEN amount ELSE 0 END) as total_volume
                FROM transactions"""
            )
            
            if transactions_stats:
                stats.update({
                    "transactions": transactions_stats['total_transactions'],
                    "completed_transactions": transactions_stats['completed_transactions'],
                    "total_volume": Decimal(transactions_stats['total_volume'] or '0')
                })

            # Статистика тикетов
            tickets_stats = await self.db.fetch_one(
                """SELECT 
                    COUNT(*) as total_tickets,
                    SUM(CASE WHEN status = 'open' THEN 1 ELSE 0 END) as open_tickets
                FROM support_tickets"""
            )
            
            if tickets_stats:
                stats.update({
                    "tickets": tickets_stats['total_tickets'],
                    "open_tickets": tickets_stats['open_tickets']
                })

        except Exception as e:
            logging.error(f"Ошибка получения статистики: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения статистики")
        
        return stats

    async def get_detailed_stats(self, period_days: int = 7) -> dict:
        """Получение детальной статистики за указанный период"""
        stats = await self.get_system_stats()
        
        try:
            # Детальная статистика пользователей
            stats['user_growth'] = await self._get_user_growth_stats(period_days)
            
            # Статистика транзакций по дням
            stats['transactions_by_day'] = await self._get_transactions_by_day(period_days)
            
            # Статистика по типам транзакций
            stats['transactions_by_type'] = await self._get_transactions_by_type(period_days)
            
            # Распределение платежей
            stats['payment_distribution'] = await self._get_payment_distribution()

        except Exception as e:
            logging.error(f"Ошибка получения детальной статистики: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения детальной статистики")
        
        return stats

    async def _get_user_growth_stats(self, period_days: int) -> List[dict]:
        """Получение статистики роста пользователей"""
        return await self.db.fetch_all(
            """SELECT 
                date(created_at) as date,
                COUNT(*) as new_users,
                SUM(COUNT(*)) OVER (ORDER BY date(created_at)) as total_users
            FROM users
            WHERE created_at > datetime('now', ?)
            GROUP BY date(created_at)
            ORDER BY date""",
            (f"-{period_days} days",)
        )

    async def _get_transactions_by_day(self, period_days: int) -> List[dict]:
        """Получение статистики транзакций по дням"""
        return await self.db.fetch_all(
            """SELECT 
                date(created_at) as date,
                COUNT(*) as count,
                SUM(amount) as volume
            FROM transactions
            WHERE created_at > datetime('now', ?)
            GROUP BY date(created_at)
            ORDER BY date""",
            (f"-{period_days} days",)
        )

    async def _get_transactions_by_type(self, period_days: int) -> List[dict]:
        """Получение статистики транзакций по типам"""
        return await self.db.fetch_all(
            """SELECT 
                type,
                COUNT(*) as count,
                SUM(amount) as volume
            FROM transactions
            WHERE created_at > datetime('now', ?)
            GROUP BY type
            ORDER BY volume DESC""",
            (f"-{period_days} days",)
        )

    async def _get_payment_distribution(self) -> List[dict]:
        """Получение распределения платежей по суммам"""
        return await self.db.fetch_all(
            """SELECT 
                CASE
                    WHEN amount < 100 THEN '0-100'
                    WHEN amount < 500 THEN '100-500'
                    WHEN amount < 1000 THEN '500-1000'
                    WHEN amount < 5000 THEN '1000-5000'
                    ELSE '5000+'
                END as range,
                COUNT(*) as count,
                SUM(amount) as volume
            FROM transactions
            WHERE status = 'completed' AND type = 'deposit'
            GROUP BY range
            ORDER BY volume DESC"""
        )

    async def get_user_list(self, page: int = 1, per_page: int = 20) -> dict:
        """Получение списка пользователей с пагинацией"""
        offset = (page - 1) * per_page
        
        try:
            users = await self.db.fetch_all(
                """SELECT 
                    user_id, 
                    username, 
                    balance, 
                    is_active,
                    date(created_at) as reg_date,
                    date(last_login) as last_login
                FROM users
                ORDER BY created_at DESC
                LIMIT ? OFFSET ?""",
                (per_page, offset)
            )
            
            total = await self.db.fetch_one("SELECT COUNT(*) as count FROM users")
            
            return {
                "users": users,
                "total": total['count'] if total else 0,
                "page": page,
                "per_page": per_page,
                "total_pages": (total['count'] + per_page - 1) // per_page if total else 1
            }
        except Exception as e:
            logging.error(f"Ошибка получения списка пользователей: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения списка пользователей")

    async def search_users(self, query: str, limit: int = 20) -> List[dict]:
        """Поиск пользователей по ID, имени или Steam логину"""
        try:
            if query.isdigit():
                # Поиск по ID
                return await self.db.fetch_all(
                    """SELECT 
                        user_id, 
                        username, 
                        balance, 
                        is_active
                    FROM users
                    WHERE user_id = ?
                    LIMIT ?""",
                    (int(query), limit)
                )
            else:
                # Поиск по имени или Steam логину
                search_pattern = f"%{query}%"
                return await self.db.fetch_all(
                    """SELECT 
                        user_id, 
                        username, 
                        balance, 
                        is_active
                    FROM users
                    WHERE username LIKE ? OR username LIKE ?
                    LIMIT ?""",
                    (search_pattern, search_pattern, limit)
                )
        except Exception as e:
            logging.error(f"Ошибка поиска пользователей: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка поиска пользователей")

    async def get_user_details(self, user_id: int) -> dict:
        """Получение детальной информации о пользователе"""
        try:
            user = await self.db.fetch_one(
                """SELECT 
                    user_id,
                    username,
                    email,
                    phone,
                    balance,
                    is_active,
                    created_at,
                    last_login,
                    failed_login_attempts,
                    mfa_secret IS NOT NULL as has_mfa
                FROM users
                WHERE user_id = ?""",
                (user_id,)
            )
            
            if not user:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Пользователь не найден")
            
            # Получаем последние транзакции пользователя
            transactions = await self.db.fetch_all(
                """SELECT 
                    transaction_id,
                    amount,
                    currency,
                    status,
                    type,
                    date(created_at) as date
                FROM transactions
                WHERE user_id = ?
                ORDER BY created_at DESC
                LIMIT 10""",
                (user_id,)
            )
            
            # Получаем открытые тикеты пользователя
            tickets = await self.db.fetch_all(
                """SELECT 
                    ticket_id,
                    text,
                    status,
                    created_at
                FROM support_tickets
                WHERE user_id = ? AND status = 'open'
                ORDER BY created_at DESC""",
                (user_id,)
            )
            
            return {
                **dict(user),
                "transactions": transactions,
                "tickets": tickets
            }
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка получения данных пользователя: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения данных пользователя")

    async def update_user_status(self, user_id: int, is_active: bool) -> bool:
        """Обновление статуса пользователя (активен/заблокирован)"""
        try:
            await self.db.execute(
                "UPDATE users SET is_active = ? WHERE user_id = ?",
                (int(is_active), user_id),
                commit=True
            )
            
            await self.db.log_audit(
                None,  # Системное действие
                "user_status_change",
                f"User {user_id} status changed to {'active' if is_active else 'inactive'}"
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка обновления статуса пользователя: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка обновления статуса пользователя")

    async def adjust_user_balance(self, user_id: int, amount: Decimal, description: str) -> dict:
        """Изменение баланса пользователя администратором"""
        if abs(amount) > self.config.MAX_MANUAL_BALANCE_CHANGE:
            raise BotError(
                ErrorCode.INVALID_AMOUNT,
                f"Сумма изменения не должна превышать {self.config.MAX_MANUAL_BALANCE_CHANGE}"
            )
        
        try:
            async with self.db.transaction() as tx:
                # Получаем текущий баланс
                user = await tx.execute_fetchone(
                    "SELECT balance FROM users WHERE user_id = ?",
                    (user_id,)
                )
                
                if not user:
                    raise BotError(ErrorCode.USER_NOT_FOUND, "Пользователь не найден")
                
                current_balance = Decimal(user['balance'])
                new_balance = current_balance + amount
                
                if new_balance < 0:
                    raise BotError(
                        ErrorCode.INVALID_AMOUNT,
                        "Итоговый баланс не может быть отрицательным"
                    )
                
                # Обновляем баланс
                await tx.execute(
                    "UPDATE users SET balance = ? WHERE user_id = ?",
                    (float(new_balance), user_id)
                )
                
                # Создаем запись о транзакции
                transaction_id = f"adm_{secrets.token_hex(8)}"
                await tx.execute(
                    """INSERT INTO transactions (
                        transaction_id, user_id, amount, status, type, description
                    ) VALUES (?, ?, ?, ?, ?, ?)""",
                    (
                        transaction_id,
                        user_id,
                        float(amount),
                        'completed',
                        'admin_adjustment',
                        description
                    )
                )
                
                await self.db.log_audit(
                    None,  # Системное действие
                    "balance_adjustment",
                    f"User {user_id} balance changed by {amount} (new balance: {new_balance})"
                )
                
                return {
                    "transaction_id": transaction_id,
                    "user_id": user_id,
                    "amount": amount,
                    "new_balance": new_balance,
                    "previous_balance": current_balance
                }
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка изменения баланса пользователя: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка изменения баланса пользователя")

    async def get_transaction_list(self, page: int = 1, per_page: int = 20, filters: dict = None) -> dict:
        """Получение списка транзакций с пагинацией и фильтрами"""
        filters = filters or {}
        offset = (page - 1) * per_page
        
        try:
            where_clauses = []
            params = []
            
            # Применяем фильтры
            if filters.get('user_id'):
                where_clauses.append("user_id = ?")
                params.append(filters['user_id'])
                
            if filters.get('type'):
                where_clauses.append("type = ?")
                params.append(filters['type'])
                
            if filters.get('status'):
                where_clauses.append("status = ?")
                params.append(filters['status'])
                
            if filters.get('date_from'):
                where_clauses.append("created_at >= ?")
                params.append(filters['date_from'])
                
            if filters.get('date_to'):
                where_clauses.append("created_at <= ?")
                params.append(filters['date_to'])
            
            where = "WHERE " + " AND ".join(where_clauses) if where_clauses else ""
            
            # Получаем транзакции
            transactions = await self.db.fetch_all(
                f"""SELECT 
                    transaction_id,
                    user_id,
                    amount,
                    currency,
                    status,
                    type,
                    wallet_address,
                    date(created_at) as date,
                    description
                FROM transactions
                {where}
                ORDER BY created_at DESC
                LIMIT ? OFFSET ?""",
                (*params, per_page, offset)
            )
            
            # Получаем общее количество
            total = await self.db.fetch_one(
                f"SELECT COUNT(*) as count FROM transactions {where}",
                tuple(params)
            )
            
            return {
                "transactions": transactions,
                "total": total['count'] if total else 0,
                "page": page,
                "per_page": per_page,
                "total_pages": (total['count'] + per_page - 1) // per_page if total else 1
            }
        except Exception as e:
            logging.error(f"Ошибка получения списка транзакций: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения списка транзакций")

    async def get_transaction_details(self, transaction_id: str) -> dict:
        """Получение детальной информации о транзакции"""
        try:
            transaction = await self.db.fetch_one(
                """SELECT 
                    t.transaction_id,
                    t.user_id,
                    u.username,
                    t.amount,
                    t.currency,
                    t.status,
                    t.type,
                    t.wallet_address,
                    t.created_at,
                    t.completed_at,
                    t.description
                FROM transactions t
                LEFT JOIN users u ON t.user_id = u.user_id
                WHERE t.transaction_id = ?""",
                (transaction_id,)
            )
            
            if not transaction:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Транзакция не найдена")
            
            return transaction
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка получения данных транзакции: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения данных транзакции")

    async def update_transaction_status(self, transaction_id: str, status: str) -> bool:
        """Обновление статуса транзакции администратором"""
        valid_statuses = ['pending', 'processing', 'completed', 'failed', 'canceled']
        
        if status not in valid_statuses:
            raise BotError(ErrorCode.INVALID_INPUT, f"Недопустимый статус: {status}")
        
        try:
            await self.db.execute(
                """UPDATE transactions 
                SET status = ?, 
                    completed_at = CASE WHEN ? = 'completed' THEN datetime('now') ELSE completed_at END
                WHERE transaction_id = ?""",
                (status, status, transaction_id),
                commit=True
            )
            
            await self.db.log_audit(
                None,  # Системное действие
                "transaction_status_change",
                f"Transaction {transaction_id} status changed to {status}"
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка обновления статуса транзакции: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка обновления статуса транзакции")

    async def get_ticket_list(self, page: int = 1, per_page: int = 20, status: str = None) -> dict:
        """Получение списка тикетов с пагинацией"""
        offset = (page - 1) * per_page
        
        try:
            where = "WHERE status = ?" if status else ""
            params = (status,) if status else ()
            
            tickets = await self.db.fetch_all(
                f"""SELECT 
                    ticket_id,
                    user_id,
                    username,
                    status,
                    created_at,
                    substr(text, 1, 100) as preview
                FROM support_tickets
                {where}
                ORDER BY created_at DESC
                LIMIT ? OFFSET ?""",
                (*params, per_page, offset)
            )
            
            total = await self.db.fetch_one(
                f"SELECT COUNT(*) as count FROM support_tickets {where}",
                params
            )
            
            return {
                "tickets": tickets,
                "total": total['count'] if total else 0,
                "page": page,
                "per_page": per_page,
                "total_pages": (total['count'] + per_page - 1) // per_page if total else 1
            }
        except Exception as e:
            logging.error(f"Ошибка получения списка тикетов: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения списка тикетов")

    async def get_ticket_details(self, ticket_id: str) -> dict:
        """Получение детальной информации о тикете"""
        try:
            ticket = await self.db.fetch_one(
                """SELECT 
                    ticket_id,
                    user_id,
                    username,
                    text,
                    status,
                    created_at
                FROM support_tickets
                WHERE ticket_id = ?""",
                (ticket_id,)
            )
            
            if not ticket:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Тикет не найден")
            
            return ticket
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка получения данных тикета: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения данных тикета")

    async def update_ticket_status(self, ticket_id: str, status: str) -> bool:
        """Обновление статуса тикета"""
        valid_statuses = ['open', 'closed', 'pending', 'resolved']
        
        if status not in valid_statuses:
            raise BotError(ErrorCode.INVALID_INPUT, f"Недопустимый статус: {status}")
        
        try:
            await self.db.execute(
                "UPDATE support_tickets SET status = ? WHERE ticket_id = ?",
                (status, ticket_id),
                commit=True
            )
            
            await self.db.log_audit(
                None,  # Системное действие
                "ticket_status_change",
                f"Ticket {ticket_id} status changed to {status}"
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка обновления статуса тикета: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка обновления статуса тикета")

    async def add_ticket_comment(self, ticket_id: str, admin_id: int, comment: str) -> bool:
        """Добавление комментария администратора к тикету"""
        try:
            # В реальной системе здесь можно сохранять комментарий в отдельной таблице
            # Для примера просто обновляем текст тикета
            await self.db.execute(
                """UPDATE support_tickets 
                SET text = text || '\n\nAdmin comment: ' || ?
                WHERE ticket_id = ?""",
                (comment, ticket_id),
                commit=True
            )
            
            await self.db.log_audit(
                admin_id,
                "ticket_comment_added",
                f"Comment added to ticket {ticket_id}"
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка добавления комментария к тикету: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка добавления комментария к тикету")

    async def notify_user(self, user_id: int, message: str) -> bool:
        """Отправка уведомления пользователю от имени администратора"""
        try:
            # В реальной системе здесь будет интеграция с системой уведомлений
            # Для примера просто логируем действие
            logging.info(f"Уведомление для пользователя {user_id}: {message}")
            
            await self.db.log_audit(
                None,  # Системное действие
                "admin_notification",
                f"User {user_id} notified with message: {message[:100]}..."
            )
            
            return True
        except Exception as e:
            logging.error(f"Ошибка отправки уведомления: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка отправки уведомления")

    async def get_audit_log(self, page: int = 1, per_page: int = 20, filters: dict = None) -> dict:
        """Получение лога аудита с пагинацией"""
        filters = filters or {}
        offset = (page - 1) * per_page
        
        try:
            where_clauses = []
            params = []
            
            # Применяем фильтры
            if filters.get('user_id'):
                where_clauses.append("user_id = ?")
                params.append(filters['user_id'])
                
            if filters.get('action_type'):
                where_clauses.append("action_type = ?")
                params.append(filters['action_type'])
                
            if filters.get('date_from'):
                where_clauses.append("created_at >= ?")
                params.append(filters['date_from'])
                
            if filters.get('date_to'):
                where_clauses.append("created_at <= ?")
                params.append(filters['date_to'])
            
            where = "WHERE " + " AND ".join(where_clauses) if where_clauses else ""
            
            # Получаем записи
            logs = await self.db.fetch_all(
                f"""SELECT 
                    log_id,
                    user_id,
                    action_type,
                    substr(action_details, 1, 100) as action_preview,
                    ip_address,
                    created_at
                FROM audit_log
                {where}
                ORDER BY created_at DESC
                LIMIT ? OFFSET ?""",
                (*params, per_page, offset)
            )
            
            # Получаем общее количество
            total = await self.db.fetch_one(
                f"SELECT COUNT(*) as count FROM audit_log {where}",
                tuple(params)
            )
            
            return {
                "logs": logs,
                "total": total['count'] if total else 0,
                "page": page,
                "per_page": per_page,
                "total_pages": (total['count'] + per_page - 1) // per_page if total else 1
            }
        except Exception as e:
            logging.error(f"Ошибка получения лога аудита: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения лога аудита")

    async def get_audit_log_details(self, log_id: int) -> dict:
        """Получение детальной информации о записи аудита"""
        try:
            log = await self.db.fetch_one(
                """SELECT 
                    log_id,
                    user_id,
                    action_type,
                    action_details,
                    ip_address,
                    user_agent,
                    created_at
                FROM audit_log
                WHERE log_id = ?""",
                (log_id,)
            )
            
            if not log:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Запись аудита не найдена")
            
            return log
        except BotError:
            raise
        except Exception as e:
            logging.error(f"Ошибка получения данных аудита: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка получения данных аудита")

    async def create_backup(self) -> str:
        """Создание резервной копии базы данных"""
        try:
            if await self.db.backup():
                return "Резервная копия успешно создана"
            else:
                raise BotError(ErrorCode.DATABASE_ERROR, "Не удалось создать резервную копию")
        except Exception as e:
            logging.error(f"Ошибка создания резервной копии: {e}")
            raise BotError(ErrorCode.DATABASE_ERROR, "Ошибка создания резервной копии")

    async def notify_admins(self, message: str, exclude_admin_id: int = None):
        """Уведомление всех администраторов"""
        if not self.config.ADMIN_IDS:
            return
            
        for admin_id in self.config.ADMIN_IDS:
            if admin_id == exclude_admin_id:
                continue
                
            try:
                logging.info(f"Уведомление администратора {admin_id}: {message}")
                # В реальной системе здесь будет отправка сообщения администратору
            except Exception as e:
                logging.error(f"Не удалось уведомить администратора {admin_id}: {e}")

class PaymentSystem:
    """Система обработки платежей с интеграцией в базу данных"""
    
    def __init__(self, db: Database, security: Security):
        self.db = db
        self.security = security
        self.config = security.config
        logging.info("Payment system initialized")
        
        # Имитация внешних платежных систем
        self.payment_processors = {
            "card": {
                "name": "Банковская карта",
                "instructions": "Переведите средства на карту 2200 **** **** 1234",
                "commission": 0.05
            },
            "qiwi": {
                "name": "QIWI Кошелек",
                "instructions": "Переведите средства на QIWI-кошелек +7*********",
                "commission": 0.03
            },
            "crypto": {
                "name": "Криптовалюта",
                "instructions": "Отправьте BTC на адрес bc1qar0srrr7xfkvy5l643lydnw9re59gtzzwf5mdq",
                "commission": 0.01
            }
        }

    async def create_payment(self, user_id: int, amount: float, method_id: str) -> dict:
        """Создание нового платежа"""
        # Валидация суммы
        if amount < self.config.MIN_PAYMENT:
            raise BotError(
                ErrorCode.INVALID_AMOUNT,
                f"Минимальная сумма платежа: {self.config.MIN_PAYMENT} RUB"
            )
        
        if amount > self.config.MAX_PAYMENT:
            raise BotError(
                ErrorCode.INVALID_AMOUNT,
                f"Максимальная сумма платежа: {self.config.MAX_PAYMENT} RUB"
            )
        
        # Проверка существования метода оплаты
        method = self.payment_processors.get(method_id)
        if not method:
            raise BotError(ErrorCode.INVALID_INPUT, "Неверный метод оплаты")
        
        # Генерация ID транзакции
        transaction_id = f"pay_{secrets.token_hex(8)}"
        
        # Сохранение транзакции в БД
        await self.db.create_transaction({
            "transaction_id": transaction_id,
            "user_id": user_id,
            "amount": amount,
            "status": "pending",
            "type": "deposit",
            "description": f"Пополнение через {method['name']}"
        })
        
        return {
            "transaction_id": transaction_id,
            "amount": amount,
            "commission": method["commission"],
            "method": method_id,
            "instruction": method["instructions"],
            "final_amount": amount * (1 - method["commission"])
        }

    async def process_withdrawal(self, transaction_id: str) -> bool:
        """Обработка вывода средств (имитация)"""
        # Получаем данные транзакции
        transaction = await self.db.fetch_one(
            "SELECT * FROM transactions WHERE transaction_id = ?",
            (transaction_id,)
        )
        
        if not transaction:
            logging.error(f"Транзакция {transaction_id} не найдена")
            return False
        
        # Имитация обработки вывода (в реальном проекте здесь будет API вывода)
        await asyncio.sleep(2)  # Имитация задержки
        
        # В 90% случаев успех, в 10% - ошибка
        success = random.random() > 0.1
        
        if success:
            await self.db.update_transaction_status(transaction_id, "completed")
            logging.info(f"Вывод {transaction_id} успешно обработан")
        else:
            await self.db.update_transaction_status(transaction_id, "failed")
            # Возвращаем средства на баланс
            await self.db.execute(
                "UPDATE users SET balance = balance + ? WHERE user_id = ?",
                (transaction["amount"], transaction["user_id"]),
                commit=True
            )
            logging.warning(f"Ошибка обработки вывода {transaction_id}")
            
        return success

    async def get_payment_history(self, user_id: int, limit: int = 10) -> List[dict]:
        """Получение истории платежей"""
        return await self.db.fetch_all(
            """SELECT 
                transaction_id, 
                amount, 
                status, 
                created_at 
            FROM transactions 
            WHERE user_id = ? AND type = 'deposit'
            ORDER BY created_at DESC 
            LIMIT ?""",
            (user_id, limit)
        )

    async def get_withdrawal_history(self, user_id: int, limit: int = 10) -> List[dict]:
        """Получение истории выводов"""
        return await self.db.fetch_all(
            """SELECT 
                transaction_id, 
                amount, 
                status, 
                created_at 
            FROM transactions 
            WHERE user_id = ? AND type = 'withdrawal'
            ORDER BY created_at DESC 
            LIMIT ?""",
            (user_id, limit)
        )

    async def check_payment_status(self, transaction_id: str) -> str:
        """Проверка статуса платежа (имитация)"""
        # В реальной системе здесь будет запрос к платежному шлюзу
        await asyncio.sleep(1)  # Имитация задержки
        
        # 80% шанс успешного платежа, 20% - в обработке
        if random.random() > 0.2:
            return "completed"
        return "pending"

    async def get_available_methods(self) -> List[dict]:
        """Получение доступных методов оплаты"""
        return [
            {
                "id": method_id,
                "name": details["name"],
                "commission": details["commission"] * 100,
                "min_amount": self.config.MIN_PAYMENT,
                "max_amount": self.config.MAX_PAYMENT
            }
            for method_id, details in self.payment_processors.items()
        ]
    """Система обработки платежей"""
    
    def __init__(self, db: Database, security: Security):
        self.db = db
        self.security = security
        self.config = security.config
        logging.info("Payment system initialized")

    async def create_payment(self, user_id: int, amount: float, method_id: str) -> dict:
        """Создание нового платежа"""
        transaction_id = f"pay_{secrets.token_hex(8)}"
        return {
            "transaction_id": transaction_id,
            "amount": amount,
            "method": method_id,
            "instruction": f"Оплатите {amount} RUB по реквизитам метода {method_id}"
        }

    async def process_withdrawal(self, transaction_id: str) -> bool:
        """Обработка вывода средств"""
        return True  # Заглушка - в реальной системе здесь будет логика обработки

    async def get_payment_history(self, user_id: int) -> List[dict]:
        """Получение истории платежей"""
        return await self.db.fetch_all(
            "SELECT * FROM transactions WHERE user_id = ? AND type = 'deposit' ORDER BY created_at DESC LIMIT 10",
            (user_id,)
        )

    async def get_withdrawal_history(self, user_id: int) -> List[dict]:
        """Получение истории выводов"""
        return await self.db.fetch_all(
            "SELECT * FROM transactions WHERE user_id = ? AND type = 'withdrawal' ORDER BY created_at DESC LIMIT 10",
            (user_id,)
        )

    async def check_payment_status(self, transaction_id: str) -> str:
        """Проверка статуса платежа"""
        return "completed"  # Заглушка - в реальной системе здесь будет проверка статуса

    async def get_available_methods(self) -> List[dict]:
        """Получение доступных методов оплаты"""
        return [
            {"id": "card", "name": "Банковская карта"},
            {"id": "qiwi", "name": "QIWI Кошелек"},
            {"id": "crypto", "name": "Криптовалюта"}
        ]

import asyncio
import logging
from aiogram import Bot, Dispatcher
from aiogram.enums import ParseMode
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram.fsm.storage.redis import RedisStorage

import asyncio
import logging
from aiogram import Bot, Dispatcher, types, F
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandStart
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram.fsm.storage.redis import RedisStorage
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup

class MainBot:
    """Основной класс бота для управления Steam-балансом"""
    
    class States(StatesGroup):
        """Группа состояний для FSM"""
        AUTH_STEAM_LOGIN = State()
        AUTH_PASSWORD = State()
        AUTH_MFA_CODE = State()
        PAYMENT_AMOUNT = State()
        PAYMENT_METHOD = State()
        WITHDRAW_AMOUNT = State()
        WITHDRAW_WALLET = State()
        SUPPORT_REQUEST = State()
        ADMIN_ACTION = State()
        ADMIN_USER_MANAGEMENT = State()
        ADMIN_BALANCE_MANAGEMENT = State()
        ADMIN_TICKET_MANAGEMENT = State()

    def __init__(self):
        """Инициализация бота и всех компонентов"""
        # Конфигурация
        self.config = Config()
        
        # Основные компоненты
        self.bot = Bot(
            token=self.config.BOT_TOKEN,
            parse_mode=ParseMode.HTML,
            session=AiohttpSession()
        )
        self.storage = RedisStorage.from_url(self.config.REDIS_URL)
        self.dp = Dispatcher(storage=self.storage)
        
        # Подсистемы
        self.db = Database()
        self.security = Security(self.config)
        self.payment = PaymentSystem(self.db, self.security)
        self.admin = AdminPanel(self.db, self.security)
        
        # Фоновые задачи
        self.background_tasks = set()
        self.task_lock = asyncio.Lock()
        
        # Лимиты операций
        self.operation_limits = {
            'payment': {
                'limit': self.config.PAYMENT_LIMIT,
                'period': self.config.PAYMENT_LIMIT_PERIOD
            },
            'withdraw': {
                'limit': self.config.WITHDRAWAL_LIMIT,
                'period': self.config.WITHDRAWAL_LIMIT_PERIOD
            }
        }
        
    async def _handle_help(self, message: types.Message):
        """Обработка команды /help"""
        help_text = """
    <b>📚 Справка по боту</b>

    <b>Основные команды:</b>
    /start - Начать работу с ботом
    /help - Получить справку
    /cancel - Отменить текущую операцию

    <b>Основные функции:</b>
    💰 Пополнить баланс - Пополнение вашего аккаунта
    💸 Вывести средства - Вывод средств на кошелек
    📊 Мой профиль - Просмотр вашего профиля
    📜 История операций - История ваших транзакций
    🆘 Поддержка - Связь с техподдержкой
    ⚙️ Настройки - Настройки аккаунта

    Для админов:
    👑 Админ-панель - Управление системой
        """
        await message.answer(help_text, parse_mode="HTML", 
                        reply_markup=self._get_main_keyboard(message.from_user.id))

        # Регистрация обработчиков
        self._register_handlers()
        
        logging.info("MainBot инициализирован")

    async def initialize(self):
        """Асинхронная инициализация компонентов"""
        try:
            await self.db.initialize()
            await self._start_background_tasks()
            logging.info("Все компоненты инициализированы")
            return True
        except Exception as e:
            logging.critical(f"Ошибка инициализации: {str(e)}")
            return False

    async def start(self):
        """Основной метод запуска бота"""
        try:
            logging.info("Запуск бота...")
            
            # Инициализация компонентов
            if not await self.initialize():
                raise RuntimeError("Ошибка инициализации компонентов")
            
            # Запуск поллинга
            await self.dp.start_polling(
                self.bot,
                allowed_updates=self.dp.resolve_used_update_types(),
                skip_updates=True,
                on_startup=self.on_startup,
                on_shutdown=self.on_shutdown
            )
            
            logging.info("Бот успешно запущен")
        except Exception as e:
            logging.critical(f"Ошибка запуска бота: {str(e)}", exc_info=True)
            raise
        finally:
            logging.info("Бот остановлен")

    async def on_startup(self):
        """Действия при запуске бота"""
        logging.info("Bot startup actions")
        if self.config.ADMIN_IDS:
            await self.bot.send_message(
                self.config.ADMIN_IDS[0],
                "🟢 Бот успешно запущен"
            )

    async def on_shutdown(self):
        """Действия при остановке бота"""
        logging.info("Bot shutdown actions")
        async with self.task_lock:
            for task in self.background_tasks:
                task.cancel()
            await asyncio.gather(*self.background_tasks, return_exceptions=True)
        
        await self.db.close()
        await self.storage.close()
        await self.bot.session.close()
        
        if self.config.ADMIN_IDS:
            await self.bot.send_message(
                self.config.ADMIN_IDS[0],
                "🔴 Бот завершает работу"
            )

    def _register_handlers(self):
        """Регистрация всех обработчиков команд и сообщений"""
    # Обработчики команд
        self.dp.message.register(self._handle_start, CommandStart())
        self.dp.message.register(self._handle_help, Command("help"))
        self.dp.message.register(self._handle_cancel, Command("cancel"))
    
    # Обработчики текстовых команд
        self.dp.message.register(self._handle_payment, F.text == "💰 Пополнить баланс")
        self.dp.message.register(self._handle_withdraw, F.text == "💸 Вывести средства")
        self.dp.message.register(self._handle_profile, F.text == "📊 Мой профиль")
        self.dp.message.register(self._handle_support, F.text == "🆘 Поддержка")
        self.dp.message.register(self._handle_settings, F.text == "⚙️ Настройки")
        self.dp.message.register(self._handle_admin_panel, F.text == "👑 Админ-панель")
        self.dp.message.register(self._handle_history, F.text == "📜 История операций")
        
        # Обработчики состояний
        self.dp.message.register(self._process_auth_steam_login, self.States.AUTH_STEAM_LOGIN)
        self.dp.message.register(self._process_auth_password, self.States.AUTH_PASSWORD)
        self.dp.message.register(self._process_auth_mfa_code, self.States.AUTH_MFA_CODE)
        self.dp.message.register(self._process_payment_amount, self.States.PAYMENT_AMOUNT)
        self.dp.message.register(self._process_payment_method, self.States.PAYMENT_METHOD)
        self.dp.message.register(self._process_withdraw_amount, self.States.WITHDRAW_AMOUNT)
        self.dp.message.register(self._process_withdraw_wallet, self.States.WITHDRAW_WALLET)
        self.dp.message.register(self._process_support_request, self.States.SUPPORT_REQUEST)
        
        # Обработчики колбэков
        self.dp.callback_query.register(
            self._handle_settings_callback, 
            F.data.startswith("settings_")
        )
        self.dp.callback_query.register(
            self._handle_admin_callback, 
            F.data.startswith("admin_")
        )
        
        # Общие обработчики
        self.dp.message.register(self._cancel_operation, F.text == "❌ Отмена")
        self.dp.message.register(self._handle_unknown_command)

async def _handle_start(self, message: types.Message, state: FSMContext):
    """Обработка команды /start"""
    try:
        user_id = message.from_user.id
        first_name = message.from_user.first_name
        logging.info(f"Обработка /start для пользователя {user_id}")
        
        # Проверяем, есть ли пользователь в базе
        user = await self.db.get_user(user_id)
        
        if not user:
            # Новый пользователь
            welcome_text = (
                f"👋 Добро пожаловать, {first_name}!\n\n"
                "Это бот для пополнения Steam-баланса. "
                "Для начала работы вам нужно зарегистрироваться.\n\n"
                "Введите ваш Steam логин:"
            )
            
            await message.answer(
                welcome_text,
                reply_markup=self._get_cancel_keyboard()
            )
            await state.set_state(self.States.AUTH_STEAM_LOGIN)
        else:
            # Существующий пользователь
            welcome_back_text = (
                f"👋 С возвращением, {first_name}!\n\n"
                f"Ваш Steam логин: {user['username']}\n"
                f"Баланс: {user.get('balance', 0):.2f} RUB\n\n"
                "Выберите действие:"
            )
            
            await message.answer
            welcome_back_text,
            reply_markup=self._get_main_keyboard(user_id)
            
        await self.db.log_audit(
            user_id,
            "start_command",
            "User used /start command"
            )
        
    except Exception as e:
        logging.error(f"Ошибка в обработчике /start: {e}")
        await message.answer(
            "⚠️ Произошла ошибка. Пожалуйста, попробуйте позже.",
            reply_markup=ReplyKeyboardRemove()
        )
        await state.clear()

    async def _run_background_task(self, task_func: Callable):
        """Безопасный запуск фоновой задачи"""
        task_name = task_func.__name__
        logging.info(f"Запуск фоновой задачи: {task_name}")
        
        while True:
            try:
                await task_func()
            except asyncio.CancelledError:
                logging.info(f"Задача {task_name} отменена")
                break
            except Exception as e:
                logging.error(f"Ошибка в фоновой задаче {task_name}: {e}")
                await asyncio.sleep(60)

    async def _task_database_backup(self):
        """Ежедневное резервное копирование БД"""
        while True:
            try:
                if await self.db.backup():
                    logging.info("Резервная копия БД успешно создана")
                await asyncio.sleep(86400)  # 24 часа
            except Exception as e:
                logging.error(f"Ошибка резервного копирования: {e}")
                await asyncio.sleep(3600)  # Повтор через час при ошибке

    async def _task_session_cleanup(self):
        """Очистка просроченных сессий"""
        while True:
            try:
                await self.db._cleanup_old_sessions()
                await asyncio.sleep(3600)  # Каждый час
            except Exception as e:
                logging.error(f"Ошибка очистки сессий: {e}")
                await asyncio.sleep(600)

    async def _task_payment_processing(self):
        """Обработка подтвержденных платежей"""
        while True:
            try:
                pending_payments = await self.db.fetch_all(
                    "SELECT * FROM transactions WHERE status = 'pending' AND created_at > datetime('now', '-1 day')"
                )
                
                if pending_payments:
                    logging.info(f"Найдено {len(pending_payments)} ожидающих платежей")
                
                for payment in pending_payments:
                    try:
                        status = await self.payment.check_payment_status(payment['transaction_id'])
                        
                        if status != payment['status']:
                            await self.db.update_transaction_status(payment['transaction_id'], status)
                            
                            if status == 'completed':
                                await self.db.execute(
                                    "UPDATE users SET balance = balance + ? WHERE user_id = ?",
                                    (payment['amount'], payment['user_id']),
                                    commit=True
                                )
                                
                                await self.bot.send_message(
                                    payment['user_id'],
                                    f"✅ Платеж #{payment['transaction_id']} на сумму {payment['amount']} RUB успешно зачислен!"
                                )
                                logging.info(f"Платеж {payment['transaction_id']} подтвержден")
                    except Exception as e:
                        logging.error(f"Ошибка обработки платежа {payment['transaction_id']}: {e}")
                
                await asyncio.sleep(300)  # Проверка каждые 5 минут
            except Exception as e:
                logging.error(f"Ошибка обработки платежей: {e}")
                await asyncio.sleep(60)

    async def _task_withdrawal_processing(self):
        """Обработка запросов на вывод средств"""
        while True:
            try:
                pending_withdrawals = await self.db.fetch_all(
                    "SELECT * FROM transactions WHERE status = 'processing' AND type = 'withdrawal'"
                )
                
                if pending_withdrawals:
                    logging.info(f"Найдено {len(pending_withdrawals)} ожидающих выводов")
                
                for withdrawal in pending_withdrawals:
                    try:
                        success = await self.payment.process_withdrawal(
                            withdrawal['transaction_id']
                        )
                        
                        if success:
                            await self.db.update_transaction_status(withdrawal['transaction_id'], 'completed')
                            
                            await self.bot.send_message(
                                withdrawal['user_id'],
                                f"✅ Вывод #{withdrawal['transaction_id']} на сумму {withdrawal['amount']} RUB выполнен!"
                            )
                            logging.info(f"Вывод {withdrawal['transaction_id']} выполнен")
                        else:
                            # Возврат средств при неудаче
                            await self.db.execute(
                                "UPDATE users SET balance = balance + ? WHERE user_id = ?",
                                (withdrawal['amount'], withdrawal['user_id']),
                                commit=True
                            )
                            await self.db.update_transaction_status(withdrawal['transaction_id'], 'failed')
                            
                            await self.bot.send_message(
                                withdrawal['user_id'],
                                f"❌ Вывод #{withdrawal['transaction_id']} не удался. Средства возвращены на баланс."
                            )
                            logging.warning(f"Вывод {withdrawal['transaction_id']} не удался")
                    except Exception as e:
                        logging.error(f"Ошибка обработки вывода {withdrawal['transaction_id']}: {e}")
                
                await asyncio.sleep(600)  # Проверка каждые 10 минут
            except Exception as e:
                logging.critical(f"CRITICAL BACKUP ERROR: {e}")
                await asyncio.sleep(60)  # Задержка перед повторной попыткой

    async def _task_check_pending_transactions(self):
        """Проверка зависших транзакций"""
        while True:
            try:
                stuck_transactions = await self.db.fetch_all(
                    """SELECT * FROM transactions 
                    WHERE status IN ('pending', 'processing') 
                    AND created_at < datetime('now', '-1 hour')"""
                )
                
                if stuck_transactions:
                    logging.warning(f"Найдено {len(stuck_transactions)} зависших транзакций")
                
                for tx in stuck_transactions:
                    try:
                        await self.db.update_transaction_status(tx['transaction_id'], 'failed')
                        
                        if tx['type'] == 'withdrawal':
                            # Возврат средств при зависшем выводе
                            await self.db.execute(
                                "UPDATE users SET balance = balance + ? WHERE user_id = ?",
                                (tx['amount'], tx['user_id']),
                                commit=True
                            )
                        
                        logging.warning(f"Транзакция {tx['transaction_id']} помечена как failed из-за таймаута")
                    except Exception as e:
                        logging.error(f"Ошибка обработки зависшей транзакции {tx['transaction_id']}: {e}")
                
                await asyncio.sleep(21600)  # Проверка каждые 6 часов
            except Exception as e:
                logging.error(f"Ошибка проверки зависших транзакций: {e}")
                await asyncio.sleep(3600)

    async def _task_recurring_payments(self):
        """Обработка периодических платежей"""
        while True:
            try:
                await self.payment.process_recurring_payments()
                await asyncio.sleep(86400)  # Раз в сутки
            except Exception as e:
                logging.error(f"Ошибка обработки периодических платежей: {e}")
                await asyncio.sleep(3600)

async def _handle_start(self, message: Message, state: FSMContext):
    """Обработка команды /start"""
    try:
        user_id = message.from_user.id
        logging.info(f"Обработка /start для пользователя {user_id}")
        
        user = await self.db.get_user(user_id)
        
        if not user:
            await self._start_new_user_flow(message, state)
        else:
            await message.answer(
                f"Добро пожаловать назад, {message.from_user.first_name}!",
                reply_markup=self._get_main_keyboard(user_id)
            )
            
    except Exception as e:
        await self._handle_error(e, message.from_user.id)

async def _handle_cancel(self, message: Message, state: FSMContext):
    """Обработка команды /cancel"""
    try:
        await state.clear()
        await message.answer(
            "❌ Текущая операция отменена",
            reply_markup=self._get_main_keyboard(message.from_user.id)
        )
        logging.info(f"Пользователь {message.from_user.id} отменил операцию")
    except Exception as e:
        await self._handle_error(e, message.from_user.id)

async def _handle_help(self, message: Message):
    """Обработка команды /help"""
    try:
        help_text = (
            "🤖 <b>Помощь по боту</b>\n\n"
            "💰 <b>Пополнение баланса</b> - пополните ваш баланс через различные платежные системы\n"
            "💸 <b>Вывод средств</b> - выведите средства на ваш крипто-кошелек\n"
            "📊 <b>Профиль</b> - просмотр вашей статистики и баланса\n"
            "📜 <b>История операций</b> - просмотр истории платежей и выводов\n"
            "🆘 <b>Поддержка</b> - связь с технической поддержкой\n"
            "⚙️ <b>Настройки</b> - настройки аккаунта и безопасности\n\n"
            "Для начала работы просто выберите нужную команду в меню."
        )
        
        await message.answer(help_text, reply_markup=self._get_main_keyboard(message.from_user.id))
        logging.info(f"Отправлена помощь пользователю {message.from_user.id}")
    except Exception as e:
        await self._handle_error(e, message.from_user.id)

    async def _handle_cancel(self, message: Message, state: FSMContext):
        """Обработка команды /cancel"""
        try:
            await state.clear()
            await message.answer(
                "❌ Текущая операция отменена",
                reply_markup=self._get_main_keyboard(message.from_user.id)
            )
            logging.info(f"Пользователь {message.from_user.id} отменил операцию")
        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _handle_payment(self, message: Message, state: FSMContext):
        """Обработка пополнения баланса"""
        try:
            user_id = message.from_user.id
            logging.info(f"Пользователь {user_id} начал пополнение баланса")
            
            if not await self.db.has_active_session(user_id):
                raise BotError(
                    ErrorCode.AUTH_REQUIRED,
                    "Требуется авторизация"
                )

            if not self.security.check_rate_limit(
                str(user_id),
                'payment',
                self.operation_limits['payment']['limit'],
                self.operation_limits['payment']['period']
            ):
                raise BotError(
                    ErrorCode.OPERATION_LIMIT,
                    "Превышен лимит операций пополнения"
                )

            await message.answer(
                f"💳 Введите сумму пополнения (от {self.config.MIN_PAYMENT} до {self.config.MAX_PAYMENT} RUB):",
                reply_markup=self._get_cancel_keyboard()
            )
            await state.set_state(self.States.PAYMENT_AMOUNT)

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _handle_withdraw(self, message: Message, state: FSMContext):
        """Обработка вывода средств"""
        try:
            user_id = message.from_user.id
            logging.info(f"Пользователь {user_id} начал вывод средств")
            
            if not await self.db.has_active_session(user_id):
                raise BotError(
                    ErrorCode.AUTH_REQUIRED,
                    "Требуется авторизация"
                )

            if not self.security.check_rate_limit(
                str(user_id),
                'withdraw',
                self.operation_limits['withdraw']['limit'],
                self.operation_limits['withdraw']['period']
            ):
                raise BotError(
                    ErrorCode.OPERATION_LIMIT,
                    "Превышен лимит операций вывода"
                )

            user = await self.db.get_user(user_id)
            balance = Decimal(user.get('balance', 0)) if user else Decimal(0)
            
            await message.answer(
                f"💰 Ваш баланс: {balance:.2f} RUB\n"
                f"Комиссия: {self.config.WITHDRAWAL_FEE*100}%\n"
                f"Введите сумму для вывода (мин. {self.config.MIN_PAYMENT} RUB):",
                reply_markup=self._get_cancel_keyboard()
            )
            await state.set_state(self.States.WITHDRAW_AMOUNT)

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _handle_profile(self, message: Message):
        """Отображение профиля пользователя"""
        try:
            user_id = message.from_user.id
            logging.info(f"Пользователь {user_id} запросил профиль")
            
            if not await self.db.has_active_session(user_id):
                raise BotError(
                    ErrorCode.AUTH_REQUIRED,
                    "Требуется авторизация"
                )

            user = await self.db.get_user(user_id)
            if not user:
                raise BotError(
                    ErrorCode.USER_NOT_FOUND,
                    "Пользователь не найден"
                )

            last_login = user.get('last_login')
            if last_login:
                last_login = datetime.fromisoformat(last_login).strftime("%d.%m.%Y %H:%M")
            else:
                last_login = "никогда"

            transactions = await self.db.fetch_all(
                "SELECT COUNT(*) as count, SUM(amount) as total FROM transactions WHERE user_id = ? AND status = 'completed'",
                (user_id,)
            )
            tx_count = transactions[0]['count'] if transactions else 0
            tx_total = Decimal(transactions[0]['total']).quantize(Decimal('0.01')) if transactions and transactions[0]['total'] else Decimal('0')
            balance = Decimal(user.get('balance', 0))
            
            profile_text = (
                f"👤 <b>Ваш профиль</b>\n\n"
                f"🆔 ID: <code>{user_id}</code>\n"
                f"📛 Имя: {message.from_user.full_name}\n"
                f"🎮 Steam: {user['username']}\n"
                f"💰 Баланс: {balance:.2f} RUB\n"
                f"📊 Всего операций: {tx_count}\n"
                f"💳 Общий оборот: {tx_total} RUB\n"
                f"🔒 2FA: {'✅ Включена' if user.get('mfa_secret') else '❌ Выключена'}\n"
                f"🛡️ Статус: {'Активен' if user.get('is_active', 1) else 'Заблокирован'}\n"
                f"⏱️ Последний вход: {last_login}"
            )

            await message.answer(
                profile_text,
                reply_markup=self._get_main_keyboard(user_id))
            logging.info(f"Профиль пользователя {user_id} отправлен")

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _handle_history(self, message: Message):
        """Отображение истории операций"""
        try:
            user_id = message.from_user.id
            logging.info(f"Пользователь {user_id} запросил историю операций")
            
            if not await self.db.has_active_session(user_id):
                raise BotError(
                    ErrorCode.AUTH_REQUIRED,
                    "Требуется авторизация"
                )

            payments = await self.payment.get_payment_history(user_id)
            withdrawals = await self.payment.get_withdrawal_history(user_id)
            
            if not payments and not withdrawals:
                await message.answer(
                    "📜 У вас пока нет операций",
                    reply_markup=self._get_main_keyboard(user_id))
                return
            
            response = ["📜 <b>История операций</b>\n"]
            
            if payments:
                response.append("\n💳 <b>Пополнения:</b>")
                for payment in payments:
                    status_icon = "✅" if payment['status'] == 'completed' else "🔄" if payment['status'] == 'pending' else "❌"
                    response.append(
                        f"{status_icon} {payment['date']}: {payment['amount']} RUB - {payment['status']}"
                    )
            
            if withdrawals:
                response.append("\n💸 <b>Выводы:</b>")
                for withdrawal in withdrawals:
                    status_icon = "✅" if withdrawal['status'] == 'completed' else "🔄" if withdrawal['status'] == 'processing' else "❌"
                    response.append(
                        f"{status_icon} {withdrawal['date']}: {withdrawal['amount']} RUB - {withdrawal['status']}"
                    )
            
            await message.answer(
                "\n".join(response),
                reply_markup=self._get_main_keyboard(user_id))
            logging.info(f"История операций пользователя {user_id} отправлена")

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _handle_support(self, message: Message, state: FSMContext):
        """Обработка обращения в поддержку"""
        try:
            user_id = message.from_user.id
            logging.info(f"Пользователь {user_id} обратился в поддержку")
            
            if not await self.db.has_active_session(user_id):
                raise BotError(
                    ErrorCode.AUTH_REQUIRED,
                    "Требуется авторизация"
                )

            await message.answer(
                "✍️ Опишите вашу проблему или вопрос:",
                reply_markup=self._get_cancel_keyboard()
            )
            await state.set_state(self.States.SUPPORT_REQUEST)

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _handle_settings(self, message: Message):
        """Отображение меню настроек"""
        try:
            user_id = message.from_user.id
            logging.info(f"Пользователь {user_id} запросил настройки")
            
            if not await self.db.has_active_session(user_id):
                raise BotError(
                    ErrorCode.AUTH_REQUIRED,
                    "Требуется авторизация"
                )

            user = await self.db.get_user(user_id)
            if not user:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Пользователь не найден")

            settings = {
                'notifications': True,  # Заглушка
                'dark_mode': False,
                'language': 'ru',
                'mfa_enabled': bool(user.get('mfa_secret'))
            }

            await message.answer(
                "⚙️ <b>Настройки аккаунта</b>",
                reply_markup=self._get_settings_keyboard(settings))
            logging.info(f"Настройки пользователя {user_id} отправлены")

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _handle_admin_panel(self, message: Message):
        """Отображение админ-панели"""
        try:
            user_id = message.from_user.id
            logging.info(f"Пользователь {user_id} запросил админ-панель")
            
            if not await self.admin.is_admin(user_id):
                raise BotError(
                    ErrorCode.PERMISSION_DENIED,
                    "Доступ запрещен"
                )

            stats = await self.admin.get_system_stats()
            
            await message.answer(
                f"👑 <b>Админ-панель</b>\n\n"
                f"👤 Пользователей: {stats['users']}\n"
                f"💸 Транзакций: {stats['transactions']}\n"
                f"🆘 Открытых тикетов: {stats['tickets']}\n"
                f"💰 Общий баланс: {stats['total_balance']} RUB",
                reply_markup=self._get_admin_keyboard())
            logging.info(f"Админ-панель отправлена пользователю {user_id}")

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _process_auth_steam_login(self, message: Message, state: FSMContext):
        """Обработка Steam логина"""
        try:
            if message.text.lower() == "отмена":
                await self._cancel_operation(message, state)
                return

            logging.info(f"Обработка Steam логина: {message.text}")
            
            if not self.security.validate_steam_login(message.text):
                raise BotError(
                    ErrorCode.INVALID_INPUT,
                    "Неверный формат Steam логина. Допустимы только буквы, цифры и _, длина 3-32 символа"
                )

            if await self.db.fetch_one("SELECT 1 FROM users WHERE username = ?", (message.text,)):
                raise BotError(
                    ErrorCode.USERNAME_EXISTS,
                    "Этот Steam логин уже используется"
                )

            await state.update_data(steam_login=message.text)
            await message.answer(
                "🔑 Придумайте надежный пароль:\n"
                "- Минимум 12 символов\n"
                "- Заглавные и строчные буквы\n"
                "- Цифры и специальные символы",
                reply_markup=self._get_cancel_keyboard()
            )
            await state.set_state(self.States.AUTH_PASSWORD)

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _process_auth_password(self, message: Message, state: FSMContext):
        """Обработка пароля"""
        try:
            if message.text.lower() == "отмена":
                await self._cancel_operation(message, state)
                return

            data = await state.get_data()
            logging.info(f"Обработка пароля для пользователя {message.from_user.id}")
            
            if 'steam_login' in data:
                await self._register_new_user(message, data, state)
            else:
                await self._authenticate_existing_user(message, state)
                
        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _process_auth_mfa_code(self, message: Message, state: FSMContext):
        """Обработка кода MFA"""
        try:
            if message.text.lower() == "отмена":
                await self._cancel_operation(message, state)
                return

            user_id = message.from_user.id
            logging.info(f"Обработка MFA кода для пользователя {user_id}")
            
            user = await self.db.get_user(user_id)
            if not user:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Пользователь не найден")
            
            if not self.security.verify_mfa_code(user['mfa_secret'], message.text):
                raise BotError(
                    ErrorCode.INVALID_MFA_CODE,
                    "Неверный код аутентификации"
                )
            
            ip_address = message.connection.signature.address if hasattr(message.connection, 'signature') else 'unknown'
            session_id = f"session_{secrets.token_hex(16)}"
            token = self.security.generate_secure_token()
            
            await self.db.execute(
                """INSERT INTO sessions (
                    session_id, user_id, token, ip_address, expires_at
                ) VALUES (?, ?, ?, ?, datetime('now', '+7 days'))""",
                (session_id, user_id, token, ip_address),
                commit=True
            )

            await message.answer(
                f"✅ Двухфакторная аутентификация успешна! Добро пожаловать, {message.from_user.first_name}!",
                reply_markup=self._get_main_keyboard(user_id))
            
            await state.clear()
            
            await self.db.log_audit(
                user_id,
                "mfa_login",
                "Successful MFA authentication"
            )
            logging.info(f"Пользователь {user_id} успешно аутентифицирован с MFA")

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _process_payment_amount(self, message: Message, state: FSMContext):
        """Обработка суммы платежа"""
        try:
            if message.text.lower() == "отмена":
                await self._cancel_operation(message, state)
                return

            try:
                amount = Decimal(message.text)
                if not (self.config.MIN_PAYMENT <= amount <= self.config.MAX_PAYMENT):
                    raise ValueError
            except (ValueError, InvalidOperation):
                raise BotError(
                    ErrorCode.INVALID_AMOUNT,
                    f"Неверная сумма. Должно быть от {self.config.MIN_PAYMENT} до {self.config.MAX_PAYMENT} RUB"
                )

            logging.info(f"Сумма платежа: {amount} RUB")
            await state.update_data(amount=amount)
            
            methods = await self.payment.get_available_methods()
            await message.answer(
                "🔘 Выберите способ оплаты:",
                reply_markup=self._get_payment_methods_keyboard(methods)
            )
            await state.set_state(self.States.PAYMENT_METHOD)

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _process_payment_method(self, message: Message, state: FSMContext):
        """Обработка выбора способа оплаты"""
        try:
            if message.text.lower() == "отмена":
                await self._cancel_operation(message, state)
                return

            data = await state.get_data()
            amount = data['amount']
            user_id = message.from_user.id
            method = message.text
            logging.info(f"Выбран способ оплаты: {method}")
            
            # Находим ID метода по названию
            method_id = None
            for m in await self.payment.get_available_methods():
                if m['name'] == method:
                    method_id = m['id']
                    break
            
            if not method_id:
                raise BotError(
                    ErrorCode.INVALID_INPUT,
                    "Неверный метод оплаты"
                )

            payment = await self.payment.create_payment(
                user_id,
                float(amount),
                method_id
            )
            
            if not payment:
                raise BotError(
                    ErrorCode.PAYMENT_FAILED,
                    "Ошибка создания платежа"
                )

            await message.answer(
                payment['instruction'],
                reply_markup=self._get_main_keyboard(user_id))
            
            await state.clear()
            
            await self.db.log_audit(
                user_id,
                "payment_created",
                f"Amount: {amount}, Method: {method}"
            )
            logging.info(f"Платеж создан: {payment['transaction_id']}")

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _process_withdraw_amount(self, message: Message, state: FSMContext):
        """Обработка суммы вывода"""
        try:
            if message.text.lower() == "отмена":
                await self._cancel_operation(message, state)
                return

            user_id = message.from_user.id
            
            try:
                amount = Decimal(message.text)
                if not (self.config.MIN_PAYMENT <= amount <= self.config.MAX_WITHDRAWAL):
                    raise ValueError
            except (ValueError, InvalidOperation):
                raise BotError(
                    ErrorCode.INVALID_AMOUNT,
                    f"Неверная сумма. Должно быть от {self.config.MIN_PAYMENT} до {self.config.MAX_WITHDRAWAL} RUB"
                )

            logging.info(f"Сумма вывода: {amount} RUB")
            user = await self.db.get_user(user_id)
            if not user:
                raise BotError(ErrorCode.USER_NOT_FOUND, "Пользователь не найден")
                
            balance = Decimal(user.get('balance', 0))
            if amount > balance:
                raise BotError(
                    ErrorCode.INSUFFICIENT_FUNDS,
                    "Недостаточно средств на балансе"
                )

            await state.update_data(amount=amount)
            await message.answer(
                "Введите адрес кошелька для вывода:",
                reply_markup=self._get_cancel_keyboard()
            )
            await state.set_state(self.States.WITHDRAW_WALLET)

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _process_withdraw_wallet(self, message: Message, state: FSMContext):
        """Обработка адреса кошелька"""
        try:
            if message.text.lower() == "отмена":
                await self._cancel_operation(message, state)
                return

            data = await state.get_data()
            amount = data['amount']
            wallet = message.text.strip()
            user_id = message.from_user.id
            logging.info(f"Адрес кошелька: {wallet}")
            
            if not self.security.validate_wallet_address(wallet):
                raise BotError(
                    ErrorCode.INVALID_WALLET,
                    "Неверный формат адреса кошелька"
                )

            async with self.db.transaction() as tx:
                withdrawal = await self.payment.create_withdrawal(
                    user_id,
                    amount,
                    wallet
                )
                
                if not withdrawal:
                    raise BotError(
                        ErrorCode.WITHDRAWAL_FAILED,
                        "Ошибка создания вывода"
                    )

                await tx.execute(
                    "UPDATE users SET balance = balance - ? WHERE user_id = ?",
                    (float(amount), user_id)
                )

                await tx.execute(
                    """INSERT INTO transactions (
                        transaction_id, user_id, amount, status, type, wallet_address
                    ) VALUES (?, ?, ?, ?, ?, ?)""",
                    (
                        withdrawal['transaction_id'],
                        user_id,
                        float(amount),
                        'processing',
                        'withdrawal',
                        wallet
                    )
                )

                await message.answer(
                    f"✅ Запрос на вывод {amount:.2f} RUB принят!\n"
                    f"Комиссия: {withdrawal['fee']:.2f} RUB\n"
                    f"К выплате: {withdrawal['net_amount']:.2f} RUB\n"
                    f"ID транзакции: {withdrawal['transaction_id']}",
                    reply_markup=self._get_main_keyboard(user_id))
                
                await self.db.log_audit(
                    user_id,
                    "withdrawal_created",
                    f"Amount: {amount}, Wallet: {wallet}"
                )
                logging.info(f"Вывод создан: {withdrawal['transaction_id']}")
            
            await state.clear()

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _process_support_request(self, message: Message, state: FSMContext):
        """Обработка текста обращения в поддержку"""
        try:
            if message.text.lower() == "отмена":
                await self._cancel_operation(message, state)
                return

            user_id = message.from_user.id
            username = message.from_user.username or message.from_user.full_name
            text = message.text[:2000]  # Ограничение длины
            logging.info(f"Обращение в поддержку от {username}")

            ticket_id = f"ticket_{secrets.token_hex(6)}"
            await self.db.execute(
                """INSERT INTO support_tickets (
                    ticket_id, user_id, username, text, status
                ) VALUES (?, ?, ?, ?, 'open')""",
                (ticket_id, user_id, username, text),
                commit=True
            )

            await message.answer(
                f"✅ Обращение #{ticket_id} создано! Ожидайте ответа.",
                reply_markup=self._get_main_keyboard(user_id))
            
            await state.clear()
            
            await self.admin.notify_admins(
                f"🆘 Новый тикет #{ticket_id}\n"
                f"От: @{username}\n"
                f"Текст: {text[:200]}..."
            )
            logging.info(f"Тикет создан: {ticket_id}")

        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _process_admin_action(self, message: Message, state: FSMContext):
        """Обработка действий администратора"""
        if message.text.lower() == "отмена":
            await self._cancel_operation(message, state)
            return

        data = await state.get_data()
        ticket_id = data.get('ticket_id')
        
        if ticket_id:
            ticket = await self.db.fetch_one(
                "SELECT user_id, username FROM support_tickets WHERE ticket_id = ?",
                (ticket_id,)
            )
            
            if ticket:
                await self.bot.send_message(
                    ticket['user_id'],
                    f"✉️ Ответ на ваш тикет #{ticket_id}:\n\n{message.text}"
                )
                
                await message.answer(
                    f"✅ Ответ на тикет #{ticket_id} отправлен пользователю @{ticket['username']}",
                    reply_markup=self._get_admin_keyboard()
                )
        
        await state.clear()

    async def _process_admin_user_management(self, message: Message, state: FSMContext):
        """Обработка управления пользователями администратором"""
        if message.text.lower() == "отмена":
            await self._cancel_operation(message, state)
            return

        search_query = message.text.strip()
        
        # Поиск пользователя
        user = None
        if search_query.isdigit():
            user = await self.db.get_user(int(search_query))
        else:
            users = await self.admin.search_users(search_query, limit=1)
            user = users[0] if users else None
        
        if not user:
            await message.answer(
                "❌ Пользователь не найден",
                reply_markup=self._get_admin_keyboard()
            )
            await state.clear()
            return
        
        # Отображение информации о пользователе
        balance = Decimal(user.get('balance', 0))
        is_active = user.get('is_active', 1)
        
        response = (
            f"👤 <b>Информация о пользователе</b>\n\n"
            f"🆔 ID: {user['user_id']}\n"
            f"🎮 Steam: {user['username']}\n"
            f"💰 Баланс: {balance:.2f} RUB\n"
            f"🛡️ Статус: {'Активен' if is_active else 'Заблокирован'}\n\n"
            "Выберите действие:"
        )
        
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(
                    text="💳 Пополнить баланс",
                    callback_data=f"admin_user_balance_{user['user_id']}"
                ),
                InlineKeyboardButton(
                    text="🔒 Заблокировать" if is_active else "🔓 Разблокировать",
                    callback_data=f"admin_user_toggle_{user['user_id']}"
                )
            ],
            [
                InlineKeyboardButton(text="⬅️ Назад", callback_data="admin_back")
            ]
        ])
        
        await message.answer(response, reply_markup=keyboard)
        await state.clear()

    async def _process_admin_balance_management(self, message: Message, state: FSMContext):
        """Обработка изменения баланса администратором"""
        if message.text.lower() == "отмена":
            await self._cancel_operation(message, state)
            return

        data = await state.get_data()
        user_id = data.get('admin_user_id')
        
        if not user_id:
            await message.answer("Ошибка: пользователь не определен")
            await state.clear()
            return

        try:
            amount = Decimal(message.text)
            if abs(amount) > self.config.MAX_MANUAL_BALANCE_CHANGE:
                raise ValueError
        except (ValueError, InvalidOperation):
            raise BotError(
                ErrorCode.INVALID_AMOUNT,
                f"Неверная сумма. Максимальное изменение: ±{self.config.MAX_MANUAL_BALANCE_CHANGE} RUB"
            )

        user = await self.db.get_user(user_id)
        if not user:
            raise BotError(ErrorCode.USER_NOT_FOUND, "Пользователь не найден")

        new_balance = Decimal(user.get('balance', 0)) + amount
        if new_balance < 0:
            raise BotError(
                ErrorCode.INVALID_AMOUNT,
                "Итоговый баланс не может быть отрицательным"
            )

        async with self.db.transaction() as tx:
            await tx.execute(
                "UPDATE users SET balance = ? WHERE user_id = ?",
                (float(new_balance), user_id)
            )
            
            transaction_id = f"adm_{secrets.token_hex(8)}"
            await tx.execute(
                """INSERT INTO transactions (
                    transaction_id, user_id, amount, status, type, description
                ) VALUES (?, ?, ?, ?, ?, ?)""",
                (
                    transaction_id,
                    user_id,
                    float(amount),
                    'completed',
                    'admin_adjustment',
                    f"Ручное изменение баланса администратором"
                )
            )

        await message.answer(
            f"✅ Баланс пользователя {user_id} изменен на {amount:.2f} RUB\n"
            f"Новый баланс: {new_balance:.2f} RUB",
            reply_markup=self._get_admin_keyboard()
        )
        
        # Уведомление пользователя
        await self.bot.send_message(
            user_id,
            f"ℹ️ Ваш баланс был изменен администратором на {amount:.2f} RUB\n"
            f"Новый баланс: {new_balance:.2f} RUB"
        )
        
        await state.clear()

    async def _process_admin_ticket_management(self, message: Message, state: FSMContext):
        """Обработка управления тикетами администратором"""
        if message.text.lower() == "отмена":
            await self._cancel_operation(message, state)
            return

        data = await state.get_data()
        ticket_id = data.get('ticket_id')
        
        if not ticket_id:
            # Поиск тикета
            ticket = await self.db.fetch_one(
                "SELECT * FROM support_tickets WHERE ticket_id = ?",
                (message.text.strip(),)
            )
            
            if not ticket:
                await message.answer(
                    "❌ Тикет не найден",
                    reply_markup=self._get_admin_keyboard()
                )
                await state.clear()
                return
            
            response = (
                f"🆘 <b>Тикет #{ticket['ticket_id']}</b>\n\n"
                f"👤 Пользователь: @{ticket['username']} (ID: {ticket['user_id']})\n"
                f"📅 Создан: {ticket['created_at']}\n"
                f"🔒 Статус: {ticket['status']}\n\n"
                f"📝 <b>Текст обращения:</b>\n"
                f"{ticket['text'][:500]}{'...' if len(ticket['text']) > 500 else ''}"
            )
            
            keyboard = InlineKeyboardMarkup(inline_keyboard=[
                [
                    InlineKeyboardButton(
                        text="✉️ Ответить",
                        callback_data=f"admin_ticket_reply_{ticket['ticket_id']}"
                    ),
                    InlineKeyboardButton(
                        text="✅ Закрыть",
                        callback_data=f"admin_ticket_close_{ticket['ticket_id']}"
                    )
                ],
                [
                    InlineKeyboardButton(text="⬅️ Назад", callback_data="admin_tickets")
                ]
            ])
            
            await message.answer(response, reply_markup=keyboard)
            await state.clear()
        else:
            # Обработка ответа на тикет
            await self.admin.add_ticket_comment(ticket_id, message.from_user.id, message.text)
            await message.answer(
                f"✅ Ответ на тикет #{ticket_id} добавлен",
                reply_markup=self._get_admin_keyboard()
            )
            await state.clear()

async def _register_new_user(self, message: Message, data: dict, state: FSMContext):
    """Регистрация нового пользователя"""
    try:
        user_id = message.from_user.id
        password = message.text
        
        # Проверяем, не существует ли уже пользователь
        existing_user = await self.db.get_user(user_id)
        if existing_user:
            raise BotError(
                ErrorCode.USERNAME_EXISTS,
                "Вы уже зарегистрированы. Введите пароль для входа."
            )

        # Проверка сложности пароля
        if len(password) < self.config.PASSWORD_MIN_LENGTH:
            raise BotError(
                ErrorCode.WEAK_PASSWORD,
                f"Пароль должен быть не менее {self.config.PASSWORD_MIN_LENGTH} символов"
            )

        # Хеширование пароля
        password_hash = self.security.hash_password(password)
        
        # Генерация MFA секрета
        mfa_secret = self.security.generate_mfa_secret()
        
        async with self.db.transaction() as tx:
            # Создание пользователя
            await tx.execute(
                """INSERT INTO users (
                    user_id, username, password_hash, salt,
                    email, phone, mfa_secret, balance
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    user_id,
                    data['steam_login'],
                    password_hash,
                    secrets.token_hex(16),
                    None,
                    None,
                    mfa_secret,
                    0
                )
            )
            
            # Генерация QR-кода для MFA
            qr_code = self.security.generate_mfa_qr(
                mfa_secret,
                data['steam_login']
            )
            
            # Отправка QR-кода пользователю
            await message.answer_photo(
                BufferedInputFile(qr_code.getvalue(), "mfa_qr.png"),
                caption="🔐 Отсканируйте QR-код в приложении аутентификации\n"
                        "Затем введите полученный код:",
                reply_markup=self._get_cancel_keyboard()
            )
            
            # Переход к состоянию ввода MFA кода
            await state.set_state(self.States.AUTH_MFA_CODE)
            
            # Логирование успешной регистрации
            await self.db.log_audit(
                user_id,
                "user_registered",
                f"Username: {data['steam_login']}"
            )
            logging.info(f"Новый пользователь зарегистрирован: {data['steam_login']}")

    except BotError as e:
        # Перехватываем известные ошибки и передаем их в обработчик
        raise e
    except Exception as e:
        # Логируем неизвестные ошибки
        logging.error(f"Ошибка регистрации пользователя: {str(e)}", exc_info=True)
        raise BotError(
            ErrorCode.UNKNOWN_ERROR,
            f"Ошибка регистрации: {str(e)}"
        )

    async def _authenticate_existing_user(self, message: Message, state: FSMContext):
        """Аутентификация существующего пользователя"""
        user_id = message.from_user.id
        
        user = await self.db.get_user(user_id)
        if not user:
            raise BotError(ErrorCode.USER_NOT_FOUND, "Пользователь не найден")
        
        if user.get('failed_login_attempts', 0) >= self.config.MAX_LOGIN_ATTEMPTS:
            raise BotError(
                ErrorCode.ACCOUNT_LOCKED,
                "Аккаунт заблокирован из-за слишком многих попыток"
            )

        if not self.security.verify_password(
            message.text,
            user['password_hash']
        ):
            await self.db.execute(
                "UPDATE users SET failed_login_attempts = failed_login_attempts + 1 WHERE user_id = ?",
                (user_id,),
                commit=True
            )
            
            attempts = user.get('failed_login_attempts', 0) + 1
            remaining = self.config.MAX_LOGIN_ATTEMPTS - attempts
            
            if remaining <= 0:
                await self.db.execute(
                    "UPDATE users SET is_active = 0 WHERE user_id = ?",
                    (user_id,),
                    commit=True
                )
                raise BotError(
                    ErrorCode.ACCOUNT_LOCKED,
                    "Аккаунт заблокирован из-за слишком многих попыток"
                )
            
            raise BotError(
                ErrorCode.AUTH_FAILED,
                f"Неверный пароль. Осталось попыток: {remaining}"
            )

        await self.db.execute(
            "UPDATE users SET failed_login_attempts = 0, last_login = CURRENT_TIMESTAMP WHERE user_id = ?",
            (user_id,),
            commit=True
        )
        
        if user.get('mfa_secret'):
            await message.answer(
                "🔐 Введите код из приложения аутентификации:",
                reply_markup=self._get_cancel_keyboard()
            )
            await state.set_state(self.States.AUTH_MFA_CODE)
            return

        ip_address = message.connection.signature.address if hasattr(message.connection, 'signature') else 'unknown'
        session_id = f"session_{secrets.token_hex(16)}"
        token = self.security.generate_secure_token()
        
        await self.db.execute(
            """INSERT INTO sessions (
                session_id, user_id, token, ip_address, expires_at
            ) VALUES (?, ?, ?, ?, datetime('now', '+7 days'))""",
            (session_id, user_id, token, ip_address),
            commit=True
        )

        await message.answer(
            f"✅ Авторизация успешна! Добро пожаловать, {message.from_user.first_name}!",
            reply_markup=self._get_main_keyboard(user_id))
        
        await state.clear()
        
        await self.db.log_audit(
            user_id,
            "user_login",
            f"IP: {ip_address}"
        )
        logging.info(f"Пользователь {user_id} успешно авторизован")

    async def _handle_settings_callback(self, callback: CallbackQuery):
        """Обработчик callback-запросов для настроек"""
        try:
            action = callback.data.split('_')[1]
            
            if action == "language":
                await callback.answer("Выбор языка (в разработке)")
            elif action == "notifications":
                await callback.answer("Настройка уведомлений (в разработке)")
            elif action == "theme":
                await callback.answer("Смена темы (в разработке)")
            elif action == "mfa":
                await self._toggle_mfa(callback)
            else:
                await callback.answer("Неизвестное действие")
                
            logging.info(f"Обработан callback настроек: {callback.data}")
            
        except Exception as e:
            await self._handle_error(e, callback.from_user.id)

    async def _toggle_mfa(self, callback: CallbackQuery):
        """Включение/выключение двухфакторной аутентификации"""
        try:
            user_id = callback.from_user.id
            user = await self.db.get_user(user_id)
            
            if not user:
                await callback.answer("Пользователь не найден", show_alert=True)
                return
            
            if user.get('mfa_secret'):
                # Отключение MFA
                await self.db.execute(
                    "UPDATE users SET mfa_secret = NULL WHERE user_id = ?",
                    (user_id,),
                    commit=True
                )
                await callback.answer("2FA отключена")
            else:
                # Включение MFA
                mfa_secret = self.security.generate_mfa_secret()
                await self.db.execute(
                    "UPDATE users SET mfa_secret = ? WHERE user_id = ?",
                    (mfa_secret, user_id),
                    commit=True
                )
    
                qr_code = self.security.generate_mfa_qr(
                    mfa_secret,
                    user['username']
                    )
    
                await callback.message.answer_photo(
                    BufferedInputFile(qr_code.getvalue(), "mfa_qr.png"),
                    caption="🔐 Отсканируйте QR-код в приложении аутентификации",
                    reply_markup=self._get_main_keyboard(user_id)
                )
                await callback.answer("2FA включена")
            
            # Обновляем клавиатуру настроек
            user = await self.db.get_user(user_id)
            settings = {
                'notifications': True,
                'dark_mode': False,
                'language': 'ru',
                'mfa_enabled': bool(user.get('mfa_secret'))
            }
            
            await callback.message.edit_reply_markup(
                reply_markup=self._get_settings_keyboard(settings)
            )
            
        except Exception as e:
            await self._handle_error(e, callback.from_user.id)

    async def _handle_admin_callback(self, callback: CallbackQuery):
        """Обработчик callback-запросов для админ-панели"""
        try:
            if not await self.admin.is_admin(callback.from_user.id):
                await callback.answer("Доступ запрещен", show_alert=True)
                return
                
            action = callback.data.split('_')[1]
            
            if action == "stats":
                await self._handle_admin_stats(callback)
            elif action == "users":
                await self._handle_admin_users(callback)
            elif action == "transactions":
                await self._handle_admin_transactions(callback)
            elif action == "tickets":
                await self._handle_admin_tickets(callback)
            elif action == "settings":
                await callback.answer("Настройки админ-панели (в разработке)")
            elif action == "backup":
                await self._handle_admin_backup(callback)
            elif action == "back":
                await self._handle_admin_back(callback)
            elif action.startswith("user"):
                await self._handle_admin_user_callback(callback)
            elif action.startswith("ticket"):
                await self._handle_admin_ticket_callback(callback)
            else:
                await callback.answer("Неизвестное действие")
                
            logging.info(f"Обработан admin callback: {callback.data}")
            
        except Exception as e:
            await self._handle_error(e, callback.from_user.id)

    async def _handle_admin_stats(self, callback: CallbackQuery):
        """Показать статистику системы"""
        stats = await self.admin.get_detailed_stats()
        text = (
            "📊 <b>Статистика системы</b>\n\n"
            f"👤 Пользователей: {stats['users']}\n"
            f"🆕 Новых за сутки: {stats.get('new_users_day', 0)}\n"
            f"🔄 Активных: {stats.get('active_users', 0)}\n\n"
            f"💸 Транзакций: {stats['transactions']}\n"
            f"💰 Общий оборот: {stats['total_balance']:.2f} RUB\n"
            f"📈 Средний платеж: {stats.get('avg_payment', 0):.2f} RUB\n\n"
            f"🆘 Открытых тикетов: {stats['tickets']}"
        )
        await callback.message.edit_text(text, reply_markup=self._get_admin_keyboard())
        await callback.answer()

    async def _handle_admin_users(self, callback: CallbackQuery):
        """Управление пользователями"""
        await callback.message.edit_text(
            "👤 <b>Управление пользователями</b>\n\n"
            "Введите ID пользователя, имя или Steam логин:",
            reply_markup=ReplyKeyboardMarkup(
                keyboard=[[KeyboardButton(text="❌ Отмена")]],
                resize_keyboard=True
            )
        )
        await callback.message.answer(
            "Можно ввести:\n- ID пользователя\n- Steam логин\n- Часть имени",
            reply_markup=ReplyKeyboardRemove()
        )
        await callback.answer()
        await self.dp.set_state(callback.from_user.id, self.States.ADMIN_USER_MANAGEMENT)

    async def _handle_admin_transactions(self, callback: CallbackQuery):
        """Управление транзакциями"""
        # В реальной реализации здесь будет полноценный интерфейс
        await callback.answer("Управление транзакциями (в разработке)")

    async def _handle_admin_tickets(self, callback: CallbackQuery):
        """Управление тикетами"""
        await callback.message.edit_text(
            "🆘 <b>Управление тикетами поддержки</b>\n\n"
            "Введите ID тикета или часть текста для поиска:",
            reply_markup=ReplyKeyboardMarkup(
                keyboard=[[KeyboardButton(text="❌ Отмена")]],
                resize_keyboard=True
            )
        )
        await callback.answer()
        await self.dp.set_state(callback.from_user.id, self.States.ADMIN_TICKET_MANAGEMENT)

    async def _handle_admin_back(self, callback: CallbackQuery):
        """Возврат в главное меню админ-панели"""
        stats = await self.admin.get_system_stats()
        
        await callback.message.edit_text(
            f"👑 <b>Админ-панель</b>\n\n"
            f"👤 Пользователей: {stats['users']}\n"
            f"💸 Транзакций: {stats['transactions']}\n"
            f"🆘 Открытых тикетов: {stats['tickets']}\n"
            f"💰 Общий баланс: {stats['total_balance']} RUB",
            reply_markup=self._get_admin_keyboard())
        await callback.answer()

    async def _handle_admin_backup(self, callback: CallbackQuery):
        """Создание резервной копии базы данных"""
        await callback.answer("Создание резервной копии...")
        
        try:
            result = await self.admin.create_backup()
            await callback.message.answer(f"✅ {result}")
        except Exception as e:
            await callback.message.answer(f"❌ Ошибка: {str(e)}")

    async def _handle_admin_user_callback(self, callback: CallbackQuery):
        """Обработка действий с пользователями"""
        action_parts = callback.data.split('_')
        user_id = int(action_parts[3])
        
        if action_parts[2] == "balance":
            await self._handle_admin_user_balance(callback, user_id)
        elif action_parts[2] == "toggle":
            await self._handle_admin_user_toggle(callback, user_id)

    async def _handle_admin_user_balance(self, callback: CallbackQuery, user_id: int):
        """Изменение баланса пользователя"""
        await callback.message.answer(
            f"💰 Текущий баланс пользователя: {await self._get_user_balance(user_id):.2f} RUB\n"
            "Введите сумму для изменения (положительную для пополнения, отрицательную для списания):",
            reply_markup=ReplyKeyboardMarkup(
                keyboard=[[KeyboardButton(text="❌ Отмена")]],
                resize_keyboard=True
            )
        )
        await self.dp.current_state().update_data(admin_user_id=user_id)
        await callback.answer()
        await self.dp.set_state(callback.from_user.id, self.States.ADMIN_BALANCE_MANAGEMENT)

    async def _handle_admin_user_toggle(self, callback: CallbackQuery, user_id: int):
        """Блокировка/разблокировка пользователя"""
        try:
            user = await self.db.get_user(user_id)
            if not user:
                await callback.answer("Пользователь не найден", show_alert=True)
                return

            new_status = not user.get('is_active', 1)
            await self.admin.update_user_status(user_id, new_status)
            
            action = "разблокирован" if new_status else "заблокирован"
            await callback.answer(f"Пользователь {action}")
            
            # Обновляем сообщение
            await self._update_user_info_message(callback.message, user_id)
        except Exception as e:
            await self._handle_error(e, callback.from_user.id)

    async def _handle_admin_ticket_callback(self, callback: CallbackQuery):
        """Обработка действий с тикетами"""
        action_parts = callback.data.split('_')
        ticket_id = action_parts[3]
        
        if action_parts[2] == "reply":
            await self._handle_admin_ticket_reply(callback, ticket_id)
        elif action_parts[2] == "close":
            await self._handle_admin_ticket_close(callback, ticket_id)

    async def _handle_admin_ticket_reply(self, callback: CallbackQuery, ticket_id: str):
        """Ответ на тикет"""
        await callback.message.answer(
            "✍️ Введите ваш ответ на тикет:",
            reply_markup=ReplyKeyboardMarkup(
                keyboard=[[KeyboardButton(text="❌ Отмена")]],
                resize_keyboard=True
            )
        )
        await self.dp.current_state().update_data(ticket_id=ticket_id)
        await callback.answer()
        await self.dp.set_state(callback.from_user.id, self.States.ADMIN_ACTION)

    async def _handle_admin_ticket_close(self, callback: CallbackQuery, ticket_id: str):
        """Закрытие тикета"""
        try:
            await self.admin.update_ticket_status(ticket_id, 'closed')
            await callback.message.edit_text(
                f"✅ Тикет #{ticket_id} закрыт",
                reply_markup=InlineKeyboardMarkup(inline_keyboard=
                    [InlineKeyboardButton(text="⬅️ Назад", callback_data="admin_tickets")]
                )
            )
            await callback.answer()
        except Exception as e:
            await self._handle_error(e, callback.from_user.id)

    async def _update_user_info_message(self, message: Message, user_id: int):
        """Обновление сообщения с информацией о пользователе"""
        user = await self.db.get_user(user_id)
        if not user:
            return

        balance = Decimal(user.get('balance', 0))
        is_active = user.get('is_active', 1)
        
        text = (
            f"👤 <b>Информация о пользователе</b>\n\n"
            f"🆔 ID: {user_id}\n"
            f"🎮 Steam: {user['username']}\n"
            f"💰 Баланс: {balance:.2f} RUB\n"
            f"🛡️ Статус: {'Активен' if is_active else 'Заблокирован'}"
        )
        
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(
                    text="💳 Пополнить баланс",
                    callback_data=f"admin_user_balance_{user_id}"
                ),
                InlineKeyboardButton(
                    text="🔒 Заблокировать" if is_active else "🔓 Разблокировать",
                    callback_data=f"admin_user_toggle_{user_id}"
                )
            ],
            [
                InlineKeyboardButton(text="⬅️ Назад", callback_data="admin_back")
            ]
        ])
        
        await message.edit_text(text, reply_markup=keyboard)

    async def _get_user_balance(self, user_id: int) -> Decimal:
        """Получение баланса пользователя"""
        user = await self.db.get_user(user_id)
        return Decimal(user.get('balance', 0)) if user else Decimal(0)

def _get_main_keyboard(self, user_id: int) -> ReplyKeyboardMarkup:
    items = [
        "💰 Пополнить баланс", "💸 Вывести средства",
        "📊 Мой профиль", "📜 История операций",
        "🆘 Поддержка", "⚙️ Настройки"
    ]
    if user_id in self.config.ADMIN_IDS:
        items.append("👑 Админ-панель")
    
    keyboard = [items[i:i+2] for i in range(0, len(items), 2)]
    return ReplyKeyboardMarkup(keyboard=keyboard, resize_keyboard=True)

def _get_cancel_keyboard(self) -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="❌ Отмена")]],
        resize_keyboard=True
    )

    def _get_payment_methods_keyboard(self, methods: list) -> ReplyKeyboardMarkup:
        """Клавиатура выбора способа оплаты"""
        buttons = []
        for method in methods:
            buttons.append([KeyboardButton(text=method['name'])])
        buttons.append([KeyboardButton(text="❌ Отмена")])
        return ReplyKeyboardMarkup(keyboard=buttons, resize_keyboard=True)

    def _get_settings_keyboard(self, settings: dict) -> InlineKeyboardMarkup:
        """Инлайн-клавиатура настроек"""
        keyboard = [
            [
                InlineKeyboardButton(text="🌐 Язык", callback_data="settings_language"),
                InlineKeyboardButton(
                    text=f"🔔 Уведомления: {'✅' if settings['notifications'] else '❌'}", 
                    callback_data="settings_notifications"
                )
            ],
            [
                InlineKeyboardButton(
                    text=f"🌙 Тема: {'Темная' if settings['dark_mode'] else 'Светлая'}", 
                    callback_data="settings_theme"
                )
            ],
            [
                InlineKeyboardButton(
                    text=f"🔒 2FA: {'✅ Вкл' if settings['mfa_enabled'] else '❌ Выкл'}", 
                    callback_data="settings_mfa"
                )
            ]
        ]
        return InlineKeyboardMarkup(inline_keyboard=keyboard)

    def _get_admin_keyboard(self) -> InlineKeyboardMarkup:
        """Инлайн-клавиатура админ-панели"""
        return InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(text="📊 Статистика", callback_data="admin_stats"),
                InlineKeyboardButton(text="👤 Пользователи", callback_data="admin_users")
            ],
            [
                InlineKeyboardButton(text="💸 Транзакции", callback_data="admin_transactions"),
                InlineKeyboardButton(text="🆘 Тикеты", callback_data="admin_tickets")
            ],
            [
                InlineKeyboardButton(text="⚙️ Настройки", callback_data="admin_settings"),
                InlineKeyboardButton(text="📁 Бэкап БД", callback_data="admin_backup")
            ]
        ])

    async def _handle_text_messages(self, message: Message):
        """Обработка текстовых сообщений без команд"""
        try:
            if not await self.db.has_active_session(message.from_user.id):
                await message.answer(
                    "Для начала работы отправьте /start",
                    reply_markup=ReplyKeyboardRemove()
                )
                return
                
            await message.answer(
                "Я не понимаю эту команду. Пожалуйста, используйте кнопки меню.",
                reply_markup=self._get_main_keyboard(message.from_user.id)
            )
        except Exception as e:
            await self._handle_error(e, message.from_user.id)

    async def _cancel_operation(self, message: Message, state: FSMContext):
        """Отмена текущей операции"""
        await state.clear()
        await message.answer(
            "❌ Операция отменена",
            reply_markup=self._get_main_keyboard(message.from_user.id))
        logging.info(f"Операция отменена пользователем {message.from_user.id}")
        
    async def _handle_unknown_command(self, message: Message):
        """Обработка неизвестных команд"""
        await message.answer(
            "🤔 Я не понимаю эту команду. Пожалуйста, используйте кнопки меню.",
            reply_markup=self._get_main_keyboard(message.from_user.id))
        logging.warning(f"Неизвестная команда от {message.from_user.id}: {message.text}")

    async def _start_new_user_flow(self, message: Message, state: FSMContext):
        """Логика для новых пользователей"""
        await message.answer(
            "👋 Добро пожаловать! Введите ваш Steam логин:",
            reply_markup=self._get_cancel_keyboard()
        )
        await state.set_state(self.States.AUTH_STEAM_LOGIN)
        
        await self.db.log_audit(
            None,
            "new_user_start",
            f"Username: {message.from_user.username}"
        )
        logging.info(f"Начата регистрация нового пользователя: {message.from_user.username}")

    async def _handle_returning_user(self, message: Message, user: dict, state: FSMContext):
        """Логика для существующих пользователей"""
        if await self.db.has_active_session(message.from_user.id):
            await message.answer(
                f"👋 С возвращением, {message.from_user.first_name}!",
                reply_markup=self._get_main_keyboard(message.from_user.id))
            logging.info(f"Пользователь {message.from_user.id} имеет активную сессию")
        else:
            await message.answer(
                "🔒 Введите ваш пароль:",
                reply_markup=self._get_cancel_keyboard()
            )
            await state.set_state(self.States.AUTH_PASSWORD)
            logging.info(f"Пользователь {message.from_user.id} требует аутентификации")

    async def _handle_error(self, error: Exception, user_id: Optional[int] = None):
        """Централизованная обработка ошибок"""
        if isinstance(error, BotError):
            await error.handle(self.bot)
        else:
            bot_error = BotError(
                ErrorCode.UNKNOWN_ERROR,
                f"Неизвестная ошибка: {str(error)}",
                user_id=user_id
            )
            await bot_error.handle(self.bot)
        logging.error(f"Обработана ошибка для пользователя {user_id}: {error}")

async def main():
    """Основная функция запуска бота"""
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
        handlers=[
            logging.FileHandler("bot.log"),
            logging.StreamHandler()
        ]
    )
    logger = logging.getLogger(__name__)
    
    try:
        logger.info("Запуск приложения...")
        bot = MainBot()
        await bot.start()
    except KeyboardInterrupt:
        logger.info("Бот остановлен пользователем")
    except Exception as e:
        logger.critical(f"Критическая ошибка: {str(e)}", exc_info=True)
    finally:
        logger.info("Приложение завершено")

if __name__ == "__main__":
    asyncio.run(main())