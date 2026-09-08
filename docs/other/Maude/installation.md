# Maude tool setup

The paths below record this workspace's September 2026 installation. Ordinary
specification tests require Python 3 and Core Maude; proof checks additionally
use Maude++ and MFE. Other tools are optional.

| Command | Recorded installation | Purpose |
| --- | --- | --- |
| `maude` | `/opt/maude-3.5.1`, also `/opt/maude` | Core Maude 3.5.1; ordinary tests |
| `maude++` | `/opt/maude++-3.5.1` | Maude++ 3.5.1; engine for MFE |
| `mfe` | `/opt/mfe-3.5.1/src/mfe.maude` | Full Maude, CRC, and SCC on Maude++ |
| `maude-tr` | `/opt/maude-transformations` | Development build with module transformations |
| `maude-itp` | `/opt/maude-itp` | ITP sources loaded by stock Maude |
| `maude-scc` | `/opt/maude-ceta-2.3` | Legacy SCC for Maude 2.3 syntax |

Launchers are under `/usr/local/bin`. Recorded Maude++ dependencies are
Yices 2.7.0 and libtecla 1.6.3, with libtecla built into `/usr/local/lib`.
`/etc/ld.so.conf.d/usr-local.conf` adds that library directory.
`/etc/profile.d/maude.sh` sets `MAUDE_LIB=/opt/maude:/opt/maude-itp`.
Exact validation tool hashes are in [inventory/source.json](inventory/source.json).

## Specification tests

From the repository root:

```sh
python3 docs/other/Maude/tools/run-tests.py --suite core
python3 docs/other/Maude/tools/run-tests.py --suite symbolic
python3 docs/other/Maude/tools/check-loads.py
```

Use `--engine /path/to/maude` for a different installation. `run-tests.py`
also accepts `MAUDE_ENGINE`.

## Proof checks

Use MFE's checkers through Maude++, rather than the standalone checker files
bundled with Maude++. Recorded standalone failures include parser errors in
`scc.maude` and an assertion abort in `scc2.maude`.

```sh
python3 docs/other/Maude/tools/run-proofs.py --suite eligible \
  --engine maude++ --mfe /opt/mfe-3.5.1/src/mfe.maude
```

For an interactive session, `mfe mymodule.maude` loads the module and MFE.
Commands use Full Maude's parentheses:

```maude
(select tool CRC .)
(ccr MYMOD .)
(select tool SCC .)
(scc MYMOD .)
```

The runner screens constructor-only modules and checks CRC before SCC.
Checker success does not establish production RAT semantics or slice refinement.
See [proofs/coverage.md](proofs/coverage.md).

## Python bindings and Lean

The recorded Python package is `maude` 1.6.0, bundling its own Maude 3.5.1+smc
runtime independently of `/opt`:

```python
import maude

maude.init()
module = maude.getModule('NAT')
term = module.parseTerm('2 + 3 * 4')
term.reduce()
print(term)  # 14
```

The recorded `maude2lean` installation uses pipx; Lean uses elan. See
[maude2lean.md](maude2lean.md) for the translation workflow and
[Lean/VALIDATION.md](Lean/VALIDATION.md) for the pinned toolchain and build status.
