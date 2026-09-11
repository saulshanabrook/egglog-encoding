################################################################################
# util.py
# A collection of utilities used in the scripts.
################################################################################

import datetime

class Id:
    """Utility class for producing unique identifiers."""
    def tid():
        """Return a new identifier based on the current local time."""
        return (str(datetime.datetime.now())
                .replace("-", "")
                .replace(":", "")
                .replace(" ", "T"))
    
class JSONSerializable:
    """An object that can be converted into json or reconstructed from json."""
    def from_json(raw):
        """Transform the specified json into an instance of this class."""
        pass

    def __init__(self): pass

    def to_json(self):
        """Transform this object into json."""
        pass
