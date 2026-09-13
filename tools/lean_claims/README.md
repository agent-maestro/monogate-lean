# lean_claims — a public "proved in Lean" label is only as good as its build today

`check_claims.py` gates a site's Lean claims against the proofs themselves. The module docstring is the
authoritative spec (registry schema, every failure code). This page covers how to use it.

## What a green result means

For every registered claim:

- the claimed theorem is **declared in the claimed file** at a **full commit sha** (read with
  `git show`, never from a working tree);
- that file **compiles** in the declared environment, and everything it imports is pinned:
  - Lean core, by the declared toolchain;
  - lake packages, by the exact revisions `lake-manifest.json` pins, checked against both the registry
    and the checkouts;
  - local modules, by `sources`. Each source tree a claim reaches (the environment's own modules, or
    a path dependency such as monogate-lean's MachLib) is declared with a repository and a full sha.
    Every reached module must be byte-identical to that revision, and `lake build --no-build` must
    report its build current;
- the theorem's **own** `#print axioms` has no `sorryAx` and nothing outside `allowed_axioms`. A file
  that compiles is not a proof of every theorem in it;
- every occurrence of a claim label in the site's sources is a registered site or an exemption with a
  reason, and every registered line is still on the page.

What it does **not** do:

- **It never builds.** A stale environment build is `ENVIRONMENT`: run `lake build` in that
  environment, then re-run. A local module that differs from its pin is `IMPORT`: review the change,
  then move the pin in `sources`.
- **It runs on this box, at deploy.** The claimed repositories are private, so public CI cannot fetch
  them.

## Use

```bash
# the gate must fire on its canaries before its green means anything. It builds a two-package canary
# workspace offline, on --project's toolchain, in about 10 s
python3 tools/lean_claims/check_claims.py --self-test --project .
# a site's registry (monogate.dev runs both from `npm run check:site`, which cf:deploy runs first)
python3 ../monogate-lean/tools/lean_claims/check_claims.py --registry scripts/lean_claims.json --root .
```

Exit codes: 0 green, 1 a claim failed, 2 could not evaluate (never a pass).

## Registries

| site | registry | claims |
|---|---|---|
| monogate.dev | `monogate-dev/scripts/lean_claims.json` | T19 strict i-unconstructibility (monogate-research `StrictBarrier.lean`); the /superbest cost theory (machlib `CostTheory.lean`) |

- **To make a claim:** add it to the registry in the same change as the page text. Use fully qualified
  theorem names and a full sha. If the claimed file imports local modules, declare their source trees
  under the environment's `sources`.
- **After `lake update` in an environment:** copy the new revisions from its `lake-manifest.json` into
  the registry's `packages`. Until then the gate reports `ENVIRONMENT`. That is deliberate, because the
  proofs were checked against the old ones.
