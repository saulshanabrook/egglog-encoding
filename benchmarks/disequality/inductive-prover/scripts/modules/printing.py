################################################################################
# printing.py
# Utilities for formatting and printing data.
################################################################################

import datetime
from . import performance

class Logger:
    """A logger for printing messages to the stdout and/or to a file."""
    def __init__(self, default_indent = "  ", output_file=None):
        self.__indent = ""
        self.__default_indent = default_indent
        self.__output_file = output_file

    def log(self, *x):
        """Print the specified objects."""
        if self.__output_file is not None:
            with open(self.__output_file, 'a') as file:
                print(self.__indent, end="", file=file)
                print(*x, file=file)
        print(self.__indent, end="")
        print(*x)
        return self

    def push(self):
        """Increase the indentation of this logger."""
        self.__indent = self.__indent + self.__default_indent
        return self

    def pop(self):
        """Decrease the indentation of this logger."""
        self.__indent = self.__indent.removeprefix(self.__default_indent)
        return self


class TableLogger:
    """A logger for printing data formatted in a table."""
    def from_cell_sizes(logger, col_sizes):
        """Return a table logger whose columns have the specified widths."""
        return TableLogger(
            logger=logger,
            cols_formats=[f"{{0:<{col_size}s}}" for col_size in col_sizes]
        )

    def __init__(self, logger, cols_formats):
        self.logger = logger
        self.cols_formats = cols_formats

    def log_row(self, *cols, cols_formats = None):
        """Print a new row in the table."""
        formats = cols_formats or self.cols_formats
        if len(formats) == len(self.cols_formats):
            if len(cols) == len(formats):
                cell_contents = [f"│ {formats[index].format(str(col))}" for (index, col) in enumerate(cols)]
                self.logger.log(*cell_contents)
                return self
            else:
                raise ValueError(f"Row has {len(formats)} columns, but received {len(cols)} values.")
        else:
            raise ValueError(f"Row has {len(self.cols_formats)} columns, but received {len(formats)} formats.")
        

class PerformanceTableLogger:
    """A table logger for performances, allowing to format performances in a table."""
    def __header_formats():
        (col0, colk) = ("{:<30s}", "{:<20s}")
        return [col0, colk, colk, colk, colk, colk, colk]

    def __header_line():
        (col0, colk) = ("─" * 30, "─" * 20)
        return [col0, colk, colk, colk, colk, colk, colk
                ]

    def __row_formats():
        (col0, col1, colk, col6) = ("{0:<30s}", "{0:<20s}", "{0:>20s}", "{0:<20s}")
        return [col0, col1, colk, colk, colk, colk, col6]

    def __duration_as_str(nanoseconds):
        seconds = nanoseconds / 1e9
        dt = datetime.datetime.fromtimestamp(seconds)
        return dt.strftime('%M:%S.%f')

    def __init__(self, console):
        self.logger = TableLogger(console, PerformanceTableLogger.__row_formats())
        self.first_log = True

    def log_performance_row(self, benchmark, performance):
        """Print a new row in the table with the data of the specified performance."""
        if self.first_log:
            self.__log_header()
        self.logger.log_row(
            benchmark,
            performance.result,
            "{0:.3f}".format(performance.n_egraphs),
            "{0:.3f}".format(performance.n_classes),
            "{0:.3f}".format(performance.n_enodes),
            "{0:.3f}".format(performance.enode_per_class()),
            PerformanceTableLogger.__duration_as_str(performance.duration_ns),
        )
        return self

    def log_line(self):
        """Print a horizontal line in the table."""
        self.logger.log_row(
            *PerformanceTableLogger.__header_line(),
            cols_formats=PerformanceTableLogger.__header_formats(),
        )
        return self

    def __log_header(self) -> None:
        """Print the header of the table."""
        self.logger.log_row(
            "Benchmark", "Result", "# Equalities", "# EClasses", "# ENodes", "NodePerClass", "Duration",
            cols_formats=PerformanceTableLogger.__header_formats(),
        )
        self.log_line()
        self.first_log = False
