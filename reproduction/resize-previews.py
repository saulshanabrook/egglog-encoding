"""Resize scientific plot PNGs for the explicit 800-pixel visual inspection."""
import json
from pathlib import Path
import sys
from PIL import Image, __version__

manifest = json.loads(Path(sys.argv[1]).read_text())
out = Path(sys.argv[1]).parent / 'previews'
out.mkdir(exist_ok=True)
for stage in manifest['stages'][1:]:
    source = Path(manifest['output_dir']) / f"{stage['label']}-slotted-comparison.png"
    with Image.open(source) as image:
        size = (800, round(image.height * 800 / image.width))
        image.resize(size, Image.Resampling.LANCZOS).save(out / f"{stage['label']}-800.png")
print(json.dumps({'pillow': __version__, 'preview_width': 800}))
