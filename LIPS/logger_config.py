import logging
from pathlib import Path

class LineFormatter(logging.Formatter):
    def format(self, record):
        # Get the base formatted message
        message = super().format(record)
        return message.replace('\n', '\n\t')
    
def setup_logger(log_file=None, log_level="WARNING"):
    """Configure and return a logger instance that can be used across the project.
    
    Args:
        log_file (str, optional): Path to log file. If None, logs only to console.
        log_level (str, optional): The logging level.
    """
    # Create logger
    logger = logging.getLogger('LIPS')
    
    # Prevent adding handlers multiple times
    if logger.hasHandlers():
        logger.handlers.clear()
    
    # Set base logging level
    logger.setLevel(log_level)
    
    # Create formatters
    console_formatter = logging.Formatter('%(levelname)s: %(message)s')
    file_formatter = LineFormatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    
    # # Create console handler, make it print out
    # console_handler = logging.StreamHandler(sys.stdout)
    # console_handler.setFormatter(console_formatter)
    # logger.addHandler(console_handler)
    
    # Create file handler if log_file is specified
    if log_file:
        log_path = Path(log_file)
        log_path.parent.mkdir(parents=True, exist_ok=True)
        # Create or truncate the file
        if log_path.exists():
            log_path.unlink()
        file_handler = logging.FileHandler(log_file)
        file_handler.setFormatter(file_formatter)
        logger.addHandler(file_handler)
    
    return logger

# Create a default logger instance
default_logger = setup_logger(log_file="./.tmp/LIPS.log") 