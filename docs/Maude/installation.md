
Installed:
- /opt/maude++-3.5.1/ — Maude++ 3.5.1 (maude.ucm.es). Launcher /usr/local/bin/maude++. Bundles scc.maude, scc2.maude, ltlr-checker.maude, ltlr-interface.maude, symbolic-checker.maude, prelude-ceta.maude; prelude adds rpo attribute.
- /opt/maude-transformations/ — Maude dev build git-400803 (Jul 22 2026) from transformations/Maude-linux.zip. Launcher /usr/local/bin/maude-tr. Prelude adds module-transformation machinery: EXTENDED-META-LEVEL, MODULE-TRANSFORMER, TUPLE, POWER, _[_](_) transformation operator, getParameters.
- Deps for maude++: yices-2.7.0 from Fedora repo (dnf), libtecla-1.6.3 built from source into /usr/local/lib (not packaged in Fedora). Added /etc/ld.so.conf.d/usr-local.conf, ran ldconfig.

Verified:
- maude++ banner: Maude++ 3.5.1 built: Jul 21 2025.
- maude-tr banner: Maude git-400803 built: Jul 22 2026. EXTENDED-META-LEVEL reduces fine.
- maude --version still 3.5.1.

Caveat, SCC inside maude++ broken here:
- scc.maude loop: (scc M .) returns ERROR: Could not parse module for every module. Its 2.x-era metaparser rejects 3.5 module format.
- scc2.maude builtin check-completeness: binary aborts with Assertion '__n < this->size()' failed on any module, even trivial one.
- prelude-ceta.maude (Maude 2.5 prelude) does not load on this binary; no -prelude flag exists.
- For working SCC use maude-scc (Maude-ceta 2.3, installed earlier). LTLR/symbolic checker in maude++ untested.

Launcher summary:

┌───────────┬───────────────────────────┐
│  Command  │           Build           │
├───────────┼───────────────────────────┤
│ maude     │ stock 3.5.1               │
├───────────┼───────────────────────────┤
│ maude++   │ Maude++ 3.5.1             │
├───────────┼───────────────────────────┤
│ maude-tr  │ transformations dev build │
├───────────┼───────────────────────────┤
│ maude-itp │ 3.5.1 + ITP               │
├───────────┼───────────────────────────┤
│ maude-scc │ Maude-ceta 2.3 SCC        │
└───────────┴───────────────────────────┘


Done. MFE 3.5.1 installed, runs on Maude++ 3.5.1, SCC + CRC verified.

Installed:
- /opt/mfe-3.5.1/ — src/mfe.maude (loader: Full Maude 3.5.1, CRChC, MTT, SCC), examples/mynat.maude, readme, license. Taken from release asset MFE.zip; GitHub tag tarball is repo with website junk, same src/.
- /usr/local/bin/mfe — launcher: maude++ [your files] /opt/mfe-3.5.1/src/mfe.maude.

Usage:
mfe mymodule.maude
MFE> (select tool SCC .)
MFE> (scc MYMOD .)
MFE> (select tool CRC .)
MFE> (ccr MYMOD .)
Full Maude syntax: commands in parentheses.
s

Note: this fixes earlier maude++ SCC caveat. Raw scc.maude in /opt/maude++-3.5.1 still broken standalone, but MFE's SCC works through Full Maude on same binary. maude-scc (Maude-ceta 2.3) now redundant for 3.x modules.


 pip install maude

  Ran 2 shell commands

Done. maude 1.6.0 installed to user site (~/.local/lib/python3.14/site-packages), bundles Maude 3.5.1+smc. Smoke test: 2 + 3 * 4 in NAT reduces to 14.

import maude
maude.init()
m = maude.getModule('NAT')
t = m.parseTerm('2 + 3 * 4'); t.reduce(); print(t)   # 14

Self-contained; no link to /opt/maude* installs. maude.init() loads its own prelude. To load your
files: maude.load('file.maude').

✻ Cooked for 15s · done 4:30 AM

❯ summarize all Maude installs and lau

Binaries (in /opt):

┌───────────────────────────────┬────────────────────────────────────┐
│              Dir              │       Build       │                    Notes                    │
├───────────────────────────────┼────────────────────────────────────┤
│ /opt/maude-3.5.1 (symlink     │ stock Maude 3.5.1 │ pre-existing                                │
│ /opt/maude)                   │                                    │
├───────────────────────────────┼───────────────────┼─────────────────────────────────────────────┤
│                               │ Ma, symbolic checker, CETA hooks.  │
│ /opt/maude++-3.5.1            │ (UCM)             │ Needs yices (dnf) + libtecla (built,        │
│                               │   lib)                             │
├───────────────────────────────┼───────────────────┼─────────────────────────────────────────────┤
│                               │ Masformations:                     │
│ /opt/maude-transformations    │ git-400803 (Jul   │ EXTENDED-META-LEVEL, TUPLE, POWER, _[_](_)  │
│                               │ 20                                 │
├───────────────────────────────┼───────────────────┼─────────────────────────────────────────────┤
│                               │ Ma                                 │
│ /opt/maude-ceta-2.3           │ (2007, static     │ old SCC, Maude 2.3 syntax only              │
│                               │ i3                                 │
└───────────────────────────────┴───────────────────┴─────────────────────────────────────────────┘

Tool sources (pure .maude):

┌────────────────┬─────────────────────────────────────────────────────────────┬─────────────┐
│      Dir       │                                │   Runs on   │
├────────────────┼─────────────────────────────────────────────────────────────┼─────────────┤
│ /opt/maude-itp │ ITP (2006/2010) +es/           │ stock 3.5.1 │
├────────────────┼─────────────────────────────────────────────────────────────┼─────────────┤
│ /opt/mfe-3.5.1 │ MFE 3.5.1: Full Ms/mynat.maude │ maude++     │
└────────────────┴─────────────────────────────────────────────────────────────┴─────────────┘

Launchers (/usr/local/bin):

┌───────────────────┬─────────────────────────────────────────────────────────────────────────┐
│      Command      │                                            │
├───────────────────┼─────────────────────────────────────────────────────────────────────────┤
│ maude             │ stock 3.5.1                                │
├───────────────────┼─────────────────────────────────────────────────────────────────────────┤
│ maude++           │ Maude++ 3.5.1                              │
├───────────────────┼─────────────────────────────────────────────────────────────────────────┤
│ maude-tr          │ transformation                             │
├───────────────────┼─────────────────────────────────────────────────────────────────────────┤
│ maude-itp [files] │ stock + load i                             │
├───────────────────┼─────────────────────────────────────────────────────────────────────────┤
│ mfe [files]       │ maude++ + mfe.CRC .), (scc M .), (ccr M .) │
├───────────────────┼─────────────────────────────────────────────────────────────────────────┤
│ maude-scc [files] │ Maude-ceta 2.3 then (scc M .)              │
└───────────────────┴─────────────────────────────────────────────────────────────────────────┘

Env: /etc/profile.d/maude.sh sets MAUDE_LIB=/opt/maude:/opt/maude-itp (new login shell).
/etc/ld.so.conf.d/usr-local.conf add.

Python: pip install maude 1.6.0, use.1+smc. Independent of /opt.

Known gaps:
- maude++ standalone scc.maude/scc2.maude: broken (parse error / assertion crash). Use mfe for SCC on
  3.x modules instead.
- maude-scc only for Maude 2.3-syntax modules; mostly redundant now.
- LTLR / symbolic checker in maude++

Saving this to memory.

