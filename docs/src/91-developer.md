# [Developer documentation](@id dev_docs)

!!! note "Contributing guidelines"
    If you haven't, please read the [Contributing guidelines](90-contributing.md) first.

If you want to make contributions to this package that involves code, then this guide is for you.

## First time clone

!!! tip "If you have writing rights"
    If you have writing rights, you don't have to fork. Instead, simply clone and skip ahead. Whenever **upstream** is mentioned, use **origin** instead.

If this is the first time you work with this repository, follow the instructions below to clone the repository.

1. Fork this repo
2. Clone your repo (this will create a `git remote` called `origin`)
3. Add this repo as a remote:

   ```bash
   git remote add upstream https://github.com/JeffreySarnoff/AIFloats.jl
   ```

This will ensure that you have two remotes in your git: `origin` and `upstream`.
You will create branches and push to `origin`, and you will fetch and update your local `main` branch from `upstream`.

## Linting and formatting

Install a plugin on your editor to use [EditorConfig](https://editorconfig.org).
This will ensure that your editor is configured with important formatting settings.

We use [https://pre-commit.com](https://pre-commit.com) to run the linters and formatters.
In particular, the Julia code is formatted using [JuliaFormatter.jl](https://github.com/domluna/JuliaFormatter.jl), so please install it globally first:

```julia-repl
julia> # Press ]
pkg> activate
pkg> add JuliaFormatter
```

To install `pre-commit`, we recommend using [pipx](https://pipx.pypa.io) as follows:

```bash
# Install pipx following the link
pipx install pre-commit
```

With `pre-commit` installed, activate it as a pre-commit hook:

```bash
pre-commit install
```

To run the linting and formatting manually, enter the command below:

```bash
pre-commit run -a
```

**Now, you can only commit if all the pre-commit tests pass**.

### Link checking locally

We use `lychee` for link checking in CI. You can run it locally to avoid waiting for CI. First, [install lychee](https://github.com/lycheeverse/lychee?tab=readme-ov-file#installation), then run against the repository root using the project config:

```bash
lychee --no-progress --config .lychee.toml .
```

The config is `.lychee.toml` at the repository root — the same file CI passes to
`lychee-action`. It holds the exclusions: the `stable` documentation URL does not resolve
before the first tagged release, and the P3109 Public PDF is served through a redirect
chain that rate-limits automated requests (what actually pins that document is the
SHA-256 in `draft_identity()`).

## Testing

The suite requires **Julia 1.12** (the package's declared floor). The full run is:

```bash
julia --project=. -e 'using Pkg; Pkg.test()'
```

`test/runtests.jl` discovers every `test/test-*.jl` file and wraps it in a `@testset`
titled from the filename — **do not add tests to `runtests.jl` itself**, add a
`test-your-topic.jl` file and it is picked up automatically.

The full run is long, because the engine is verified against an independent `BigInt`
reference over millions of decisions. While iterating, run only the files your change
touches:

```bash
julia --project=. -e 'using Test, AIFloats; include("test/test-projection.jl")'
```

| Change touches | Run at least |
|:--|:--|
| formats, traits, validity | `test-binary-format.jl`, `test-traits.jl` |
| datums, encode/decode | `test-binaryvalue.jl`, `test-codec.jl` |
| rounding, saturation, `project` | `test-projection.jl`, `test-rounding-paths.jl` |
| the operation register | `test-ops.jl`, `test-fastpaths.jl` |
| array kernels, tables | `test-kernels.jl`, `test-tables.jl` |
| blocks, packed storage | `test-blocks.jl` |
| Base surface, promotion | `test-compat.jl`, `test-singletons.jl` |
| conformance, κ | `test-governance.jl` |
| the vendored carrier | `test-dyadic.jl` |
| exports, docstrings, Aqua/JET | `test-quality.jl` |
| anything the documentation asserts | `test-doc-contracts.jl` |

A documentation-only change does not need `Pkg.test()`. Run the doctests and the docs
build instead — see *Documentation* below.

## Benchmarking

Chairmarks lives in `benchmark/Project.toml` and is deliberately **not** a dependency of
the package or of the docs. Run the suite in its own environment:

```bash
julia --project=benchmark -t 4 benchmark/runbenchmarks.jl            # every suite
julia --project=benchmark -t 4 benchmark/runbenchmarks.jl scalar     # one suite
```

The suites are `scalar`, `arrays`, and `latency`. Four threads unless
`JULIA_NUM_THREADS` says otherwise, whatever the machine's core count: the threading rows
exist to be compared against each other and against `THREAD_MIN_ELEMS`, which was fitted
at four threads, and a machine-dependent count makes two builds incomparable.

**Run it from a clean commit.** The generated page records the commit it measured and
marks a dirty tree; a row from a dirty or older tree is historical evidence, not a
description of the code you are reading. Never hand-copy a number from it into prose —
link to the row instead.

## Continuous integration

| Workflow | What it runs |
|:--|:--|
| `Test.yml` / `TestOnPRs.yml` | the package test suite via `ReusableTest.yml`, on Julia 1.12 and `1` |
| `Docs.yml` | the documentation build, including doctests |
| `Lint.yml` | pre-commit hooks and the `lychee` link check |
| `CompatHelper.yml`, `TagBot.yml` | dependency bounds and release tagging |

Codecov runs on the Julia `1` / `ubuntu-latest` cell only.

## Working on a new issue

We try to keep a linear history in this repo, so it is important to keep your branches up-to-date.

1. Fetch from the remote and fast-forward your local main

   ```bash
   git fetch upstream
   git switch main
   git merge --ff-only upstream/main
   ```

2. Branch from `main` to address the issue (see below for naming)

   ```bash
   git switch -c 42-add-answer-universe
   ```

3. Push the new local branch to your personal remote repository

   ```bash
   git push -u origin 42-add-answer-universe
   ```

4. Create a pull request to merge your remote branch into the org main.

### Branch naming

- If there is an associated issue, add the issue number.
- If there is no associated issue, **and the changes are small**, add a prefix such as "typo", "hotfix", "small-refactor", according to the type of update.
- If the changes are not small and there is no associated issue, then create the issue first, so we can properly discuss the changes.
- Use dash separated imperative wording related to the issue (e.g., `14-add-tests`, `15-fix-model`, `16-remove-obsolete-files`).

### Commit message

- Use imperative or present tense, for instance: *Add feature* or *Fix bug*.
- Have informative titles.
- When necessary, add a body with details.
- If there are breaking changes, add the information to the commit message.

### Before creating a pull request

!!! tip "Atomic git commits"
    Try to create "atomic git commits" (recommended reading: [The Utopic Git History](https://blog.esciencecenter.nl/the-utopic-git-history-d44b81c09593)).

- Make sure the tests pass.
- Make sure the pre-commit tests pass.
- Fetch any `main` updates from upstream and rebase your branch, if necessary:

  ```bash
  git fetch upstream
  git rebase upstream/main BRANCH_NAME
  ```

- Then you can open a pull request and work with the reviewer to address any issues.

## Documentation

Set up the docs environment once:

```bash
julia --project=docs -e 'using Pkg; Pkg.develop(path = "."); Pkg.instantiate()'
```

Build the site:

```bash
AIFLOATS_DOCS_BENCHMARKS=0 julia --project=docs docs/make.jl
```

`AIFLOATS_DOCS_BENCHMARKS=0` skips the benchmark run, which is what you want for ordinary
prose work — it takes minutes, and the previously generated `60-benchmarks.md` is left
untouched rather than overwritten with a placeholder. Leave the variable unset when you
actually intend to regenerate measurements.

Two pages are **generated** by `docs/make.jl` and must not be hand-edited:

- `docs/src/60-benchmarks.md` — the benchmark run;
- `docs/src/95-reference/*.md` and the `95-reference.md` landing page — the public API
  listing, built from `Base.isexported` and `Base.ispublic`. The build **fails** if a
  public binding is neither documented nor listed in `REFERENCE_EXEMPT`.

The page tree is explicit in `docs/make.jl` (`PAGES`). Adding a page means adding a line
there; the build fails if `docs/src` holds a Markdown file `PAGES` does not list, which is
what keeps planning documents out of the published site.

Run the source doctests on their own — much faster than a full build:

```bash
julia --project=docs -e 'using Documenter: DocMeta, doctest; using AIFloats; DocMeta.setdocmeta!(AIFloats, :DocTestSetup, :(using AIFloats); recursive=true); doctest(AIFloats)'
```

For live preview, `julia --project=docs` then `using LiveServer; servedocs()`.

## Making a new release

AIFloats.jl is **not yet in the General registry**. Until it is, a release is the
version bump, the changelog entry, and the tag; the registrator steps below apply from
the first registration onward.

To create a new release:

- Create a branch `release-x.y.z`
- Update `version` in `Project.toml`
- Update the `CHANGELOG.md`:
  - Rename the section "Unreleased" to "[x.y.z] - yyyy-mm-dd" (i.e., version under brackets, dash, and date in ISO format)
  - Add a new section on top of it named "Unreleased"
  - Add a new link in the bottom for version "x.y.z"
  - Change the "[unreleased]" link to use the latest version - end of line, `vx.y.z ... HEAD`.
- Create a commit "Release vx.y.z", push, create a PR, wait for it to pass, merge the PR.
- Go back to main screen and click on the latest commit (link: <https://github.com/JeffreySarnoff/AIFloats.jl/commit/main>)
- At the bottom, write `@JuliaRegistrator register`

After that, you only need to wait and verify:

- Wait for the bot to comment (should take < 1m) with a link to a PR to the registry
- Follow the link and wait for a comment on the auto-merge
- The comment should say that all is well, and auto-merge should follow shortly
- After the merge happens, TagBot will trigger and create a new GitHub tag. Check on <https://github.com/JeffreySarnoff/AIFloats.jl/releases>
- After the release is created, a "docs" GitHub action starts for the tag.
- After it passes, a deploy action will run.
- After that runs, the [stable docs](https://JeffreySarnoff.github.io/AIFloats.jl/stable) should be updated. Check them and look for the version number.
