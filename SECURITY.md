# Security policy

## ⚠️ Status: unaudited, experimental

LEMMA is **research software built on a prototype compiler**. It has **not been audited**.
**Do not use it with real funds or deploy it to mainnet** until it has been independently audited.
Nothing in this repository deploys to mainnet or touches real value: programs run in LiteSVM, in
LEMMA's test interpreter, or on a local validator.

## Threat model

LEMMA aims to prevent these classes of on-chain bugs, and says for each program whether it does so
by **proof** or by **runtime check plus attack test** (see [`docs/audit-checklist.md`](docs/audit-checklist.md)):

- missing signer, owner or writable checks;
- account type confusion and re-initialization;
- duplicate-account aliasing;
- arithmetic overflow and rounding in the attacker's favour;
- arbitrary CPI targets;
- account revival on close;
- loss of rent exemption;
- unbounded loops.

Out of scope, and **trusted rather than proven** (details in [`docs/specs/trusted-base.md`](docs/specs/trusted-base.md)):

- the Lean kernel;
- the lean-svm compiler and ELF encoder. These are not verified end to end, and LEMMA has already
  found and patched two miscompilation bugs in them;
- the Solana runtime, loader, syscalls and CPI targets;
- anything a specification doesn't state.

A machine-checked theorem guarantees exactly its statement, under these assumptions, and nothing
more.

## Reporting a vulnerability

Please report security issues **privately** using GitHub's
[private vulnerability reporting](https://docs.github.com/en/code-security/security-advisories/guidance-on-reporting-and-writing-information-about-vulnerabilities/privately-reporting-a-security-vulnerability)
on this repository (the **Security** tab, then **Report a vulnerability**). Don't open a public
issue for an unfixed vulnerability.

The following are especially valuable:
- a compiled LEMMA program behaving differently from its Lean definition (a miscompilation);
- a theorem whose statement doesn't mean what `docs/specs/README.md` says it means;
- a vacuous theorem whose hypotheses can never hold;
- a way around a proven guard.

## Repository hygiene

- **Secrets:** gitleaks runs in CI over the full history, and as a pre-commit hook after
  `scripts/install-hooks.sh`. The ruleset includes Solana keypair files. Test keypairs are
  generated at runtime and never committed. `.gitignore` excludes `.env*`, keys and keypair JSON.
- **Supply chain:** the Lean toolchain, Solana platform-tools and gitleaks are downloaded at pinned
  versions and verified against pinned SHA-256 checksums. GitHub Actions are pinned to full commit
  SHAs. `Cargo.lock` is committed and audited with `cargo audit` in CI.
- **No telemetry:** no LEMMA tool makes network calls.
- **Proof integrity:** CI fails on `sorry`, `admit`, custom axioms, native-evaluation axioms, or
  `Nat` arithmetic reachable from on-chain code (`lake exe lemma-audit`).
