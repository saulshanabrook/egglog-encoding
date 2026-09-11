# Removed raw timing results

Raw Hyperfine JSON is generated under `/tmp` and is not tracked. The historical
report prose retains methods and summaries; this registry preserves the hashes
that were formerly stored in per-report `SHA256SUMS` files.

## Relational NEE follow-up

| File | SHA-256 |
| --- | --- |
| `propel-gset-forward.json` | `7b40a5bbcc3abbd1a704256dc51c5e768b96fd63f2a2b9e8a6470712efb9593e` |
| `propel-gset-reverse.json` | `26b35190703e0bbaa8598946c174feb4a901c1820ea7aa9c3ff40bf0f7d36a01` |
| `propel-medium-forward.json` | `06cb5c79e0a590e46684fea76dda145845b1fa8432ae0541c9386845b291149c` |
| `propel-medium-reverse.json` | `2831138a90ccc5c8828b185a90180917ccea5f6edd480268604d95af8840c632` |

## Set-backed DE follow-up

| File | SHA-256 |
| --- | --- |
| `parameter-de-timing.json` | `ffe05b8f568641a57828a7364b51313d52439b4d9df4b63b065bf4472db25e0a` |
| `parameter-ee-timing.json` | `4ea4dfa3695a4684990b49fd958286fa3e0a63a873c87f59382657d74587e5e5` |
| `parameter-forward.json` | `91f88f23527bfed2fbbc2bebf3912406fb21fd693140d7214d350e8310d39475` |
| `parameter-nee-timing.json` | `c55edef6f881b8d29b47d0c31338490b2a337547ac097ae1efbf0d6cdac155eb` |
| `parameter-oee-timing.json` | `e3d5b5b1880410571edd8d37ad3887385affa98afaecef212f5a8b93f2aa7f38` |
| `parameter-reverse.json` | `d40542257eb9b6efe87536d5c38118d6af48ef84b2a0a10d9d9aceaaf5447b86` |
| `propel-gset-forward.json` | `aa37b7fa9ede74c34d5c0e6c6ff6e8e8cd5681433ca2d8bc14d85e9bc727cf4c` |
| `propel-gset-reverse.json` | `72f9a359088fe9d2024811ade75a9285f09de996223a9d18bf70961bd057a19d` |
| `propel-medium-forward.json` | `8c8845394bc749b7a402d4db92db4562d47f763243526de2fda7a6c4097b06ea` |
| `propel-medium-reverse.json` | `2f9b23d9c6f597a4628bfba0cba59c216dd940a008b23390235304ed58154b04` |

## Term-language performance

| File | SHA-256 |
| --- | --- |
| `euf-large-forward.json` | `a90f15409397ac7a9274b222b794f5885a8b44813e60f5d34fbeb916dee5917d` |
| `euf-large-reverse.json` | `08d490d052341d0f6ea10c7ba43d5398a5fd4b61ec389535131c130885878230` |
| `euf-small-forward.json` | `952e43c16094c3d116164d172cee0e5376626f4345b2a9a29e96b8c429112252` |
| `euf-small-reverse.json` | `7581a2f6a6adaffc30abab1b75e633101673a2b6688148b85a8a56466c95da82` |
| `propel-gset-forward.json` | `a403eea7c4170022b9a072c215324f9355579ed1726fd3539d18cd90108bc2d7` |
| `propel-gset-reverse.json` | `541072ab1f6bc93aa9cb18190b5aa778c4e66bb0e62ba923d1c1a7d3e573048e` |
| `propel-medium-forward.json` | `813d2c00d5b8fe88187cf9f7c0b9645f545bc5da7a94492a7135d79017ad5cb5` |
| `propel-medium-reverse.json` | `ad03125d2e0800411b0779c12cb89a7ff86d12e2d3306d5dd86220575486247a` |
| `provenance.json` | `8194d21b32dc0ab8d37cee0087e812d617327f5aa7363b77996a948bace8f0ab` |

## Earlier typed-host-AST follow-up

| File | SHA-256 |
| --- | --- |
| `euf-small-forward.json` | `a32c390ddb2d555019246be4f030ef087d39204f65f9b181c9c7876ea9cb557c` |
| `euf-small-reverse.json` | `36ba6947a7fb1a0e59049fcdef3826d44aadab293791bbc78b6051f8ca4793e2` |
| `propel-gset-forward.json` | `70f1a06a0c7a57ec101fa9984599fcc29ecb0fca75d30d20f3e7c337f5726ff3` |
| `propel-gset-reverse.json` | `0c5455df9a402c1787580c8b3b4b9dcfa3eaadf2b311f2b23569e70c3f32837e` |
| `propel-medium-forward.json` | `4ac828fc219054b3ba396d70e28e27c10367203ff338a1f1a6a9c4ae68183431` |
| `propel-medium-reverse.json` | `204bacf14e249e8e055b8e13ecf6e415e53eaff5d2d183d5351962e57106b9ed` |
| `provenance.json` | `2aea30e9150236c7616dd32791d31340349b1d9fad0ca8712f4f2e9b7d010ca5` |
| `recording-overhead-forward.json` | `812eeae50c6a41c0c42225f6ee43a0eceeb1646d2a521ca32f7bdd8c66ff1c15` |
| `recording-overhead-reverse.json` | `2a546ddb05b980450f196be770e434709de695aed5657f3ca90b0bcec2f4dbb5` |

The current post-merge AST-first run has its own machine-local hashes in
[`ast-first-host/README.md`](ast-first-host/README.md).
