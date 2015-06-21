"""
Logging facility for the BotFarm
"""

import logging
import logging.handlers
import abc

from logging.handlers import SocketHandler, DEFAULT_TCP_LOGGING_PORT


class LogFormatter(logging.Formatter):
    FORMAT = ("[%(levelname)s]  "
            " %(asctime)s"
           " %(module)s\t"
           " %(lineno)d\t"
            "[%(message)s ]")

    BLACK, RED, GREEN, YELLOW, BLUE, MAGENTA, CYAN, WHITE = range(8)

    RESET_SEQ = "\033[0m"
    COLOR_SEQ = "\033[1;%dm"
    BOLD_SEQ = "\033[1m"

    COLORS = {
              'WARNING': YELLOW,
              'INFO': WHITE,
              'DEBUG': BLUE,
              'CRITICAL': YELLOW,
              'ERROR': RED
              }

    def _mkFormat(self, msg, color=True):
        if color:
            msg = msg.replace("$RESET", self.RESET_SEQ).replace("$BOLD", self.BOLD_SEQ)
        else:
            msg = msg.replace("$RESET", "").replace("$BOLD", "")
        return msg

    def __init__(self, color=True):
        msg = self._mkFormat(self.FORMAT, color)
        logging.Formatter.__init__(self, msg)
        self.use_color = color

    def format(self, record):
        levelname = record.levelname
        if self.use_color and levelname in self.COLORS:
            fore_color = 30 + self.COLORS[levelname]
            levelname_color = self.COLOR_SEQ % fore_color + levelname + self.RESET_SEQ
            record.levelname = levelname_color
        return logging.Formatter.format(self, record)


class Log(object):

    file_format = logging.Formatter("[%(levelname)s] %(asctime)s\
                                     %(module)s\t %(lineno)d\t [%(message)s]")

    def __init__(self):
        return

    def mk_log(self, moduleName):
        log = logging.getLogger(moduleName)
        streamhandler = logging.StreamHandler()

        log.setLevel(logging.INFO)
        streamhandler.setFormatter(LogFormatter())
        streamhandler.setLevel(logging.DEBUG)
        if len(log.handlers) == 0:
            log.addHandler(streamhandler)
            #webViewLogger.addHandler(socketh)
        return log

    def disable_log(self):
        logging.disable(logging.WARNING)



"""
An abstract Logger class. Here we will use the logger python module
"""

class LoggingManager(object):
    __metaclass__ = abc.ABCMeta

    def __init__(self):
        return

    @abc.abstractmethod
    def mk_log(self, moduleName):
        return

    @staticmethod
    def get_logger(name):
        logger = Log()
        return logger.mk_log(name)

    @staticmethod
    def disable_logger():
        logger = Log()
        return logger.disable_log()
