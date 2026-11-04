from pathlib import Path
import importlib.util
ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('capture',ROOT/'run.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
c.ENV.update(UV_CACHE_DIR='/private/tmp/encoding-parts32-candidate/.uv-cache',UV_PYTHON='3.12')
c.run('engine-make-check-process-access',['make','check'],3600,cwd=Path('/private/tmp/encoding-parts32-candidate'),check=False)
