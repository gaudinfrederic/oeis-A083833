# Palindromes p with kp+1 palindromic - consolidated Lean 4 verification record

This record contains the unified article and its machine-checked
formalization (Lean 4 + mathlib, toolchain
`leanprover/lean4:v4.35.0`) for the eleven OEIS entries of the
affine palindrome family `kp+1`: A069881 (k=2), A083829 and its
image A083830 (k=3), A083831 and its image A083832 (k=4),
A083833 and its image A083834 (k=5), A083835 and its image
A083836 (k=6), and the smallest-witness entries A083837 /
A083838 over k.

**Claims resolved here.** Every published conjecture recorded on
these entries is proved and kernel-certified:

- A069881 - the *Tangente* problem 8154 (after J. McCann's 2002
  comment): the even-length members are exactly the repdigits
  `55...5`, certified as an iff in both directions;
- A083829 - R. Israel's four observations of Feb 23 2023
  (tagged "It appears"): even-length terms are the repdigits
  `77...7` (A002281); non-repdigit terms of length >= 2 start
  with `14,15,16,24,25` or `26`; no term contains `3,8,9`; a
  term containing `7` is all `7`s;
- A083831 - R. Israel's observation of Apr 4 2018: the
  even-length terms are exactly the repdigits `88...8`;
- A083833 / A083834 - M. S. Branicky's conjectures C1/C2 of
  Jun 13 2021: digits of `p` in `{0,1,2,3}`, the only
  even-length term of `p` is the repdigit `22...2`, and the
  image claims (digits `{0,1,5,6}`, repunit `11...1`);
- A083835 / A083836 (k=6) - a complete iff classification
  (repdigit `99...9` overflow branch `q = 5 9^{m-1} 5`, or odd
  length with alternating digit classes `{0,1}` / `{2,3}`),
  with the A083836 image companions;
- A083837 / A083838 - the twenty-one displayed zeros at
  `k in {12,17,23,31,37,41,42,48,51,53,61,64,71,74,79,81,86,91,
  96,101,103}`: each is upgraded from Chandler's 2003
  finite-search comment ("0 ... indicates no palindrome
  < 10^15") to a universal nonexistence theorem via a
  prefix-suffix obstruction (`revW` / `okP` / `escapesIn`),
  with the twenty-one image corollaries for A083838.

## Contents

### Paper

| File | Role |
|---|---|
| `A083833-UNIFIE-paper.pdf` | The article (15 pp., compiled from the shipped sources) |
| `A083833-UNIFIE-paper.tex` | LaTeX master file |
| `sec-carry.tex`, `sec-A069881.tex`, `sec-A083829.tex`, `sec-A083831.tex`, `sec-A083833.tex`, `sec-A083835.tex`, `sec-zeros.tex` | Section fragments, pulled in by `\input` from the master file |

*Flat-layout note:* in the source tree the fragments live under
`sections/`; in this flat archive they sit beside the master file
and the `\input{sections/sec-X}` lines were adjusted to
`\input{sec-X}` (see the NOTE comment in the .tex header). The
shipped PDF was compiled by tectonic from exactly these flat
sources (0 errors; two cosmetic underfull-hbox warnings). Each
fragment also compiles standalone (`\@ifundefined` guards on the
theorem environments).

### Lean modules (53)

| File(s) | Role |
|---|---|
| `A069881.lean`, `A083829.lean`, `A083831.lean`, `A083833.lean`, `A083835.lean` | Per-multiplier classification modules (each carries its own copy of the carry-chain machinery - duplicated per k, not parametrized) |
| `A083830.lean`, `A083832.lean`, `A083834.lean`, `A083836.lean` | Thin image-sequence re-export modules |
| `Repdigits_KP1.lean` | Converse module: the four literal repdigit iffs (`repdigit5/7/8/2_iff_member_even_A069881/A083829/A083831/A083833` + overflow iff at k=2) |
| `A083837.lean` | Obstruction module: generic machine + `no_wit_<k>` + `A083837_<k>_zero` for the 21 indices |
| `A083838.lean` | The 21 image corollaries `A083838_<k>_zero` |
| `Spec_A######.lean` (11) | Frozen verbatim spec declarations (`SpecProp`-style `SpecA######` records, zero tactics) |
| `Check_Spec_A######.lean` (11) | Spec-faithfulness closures `proven_A######` |
| `Check_AntiVacuite_A######.lean` (10: all but A083838) | Non-vacuity witnesses + guard ablations |
| `Check_d2plus_A069881.lean` | A069881 list anchors (certified members / non-members of the displayed data) |
| `AxiomsReport_A######.lean` (8: A083829-35, A083837) | `#print axioms` audit harnesses |

### Build configuration

| File | Role |
|---|---|
| `lakefile.toml` | Consolidated build file - one `[[lean_lib]]` per shipped module (53 targets, all in `defaultTargets`) |
| `lake-manifest.json` | Pinned dependencies: mathlib `v4.35.0` (rev `56a005855e...`) and its transitive deps |
| `lean-toolchain` | `leanprover/lean4:v4.35.0` |

### Audit evidence

| File(s) | Role |
|---|---|
| `axioms-A######.txt` (11) | Per-entry kernel axiom reports: `[propext, Classical.choice, Quot.sound]` at most on every audited declaration; zero `sorryAx`, zero `ofReduceBool`/`native_decide` |
| `seal-A083833.txt`, `seal-A083834.txt` | Three-kernel seal reports (leanexport + nanoda + con-leche + con-ron, all exit 0) for the A083833/A083834 development |
| `anteriorite-A######.md` (7: A069881, A083829-34) | Prior-art audits reproduced verbatim from the original per-entry deposits |
| `oeis-verbatim.txt` | Verbatim internal-format dumps of all eleven entries (`=== A###### ===` sections), the audited source text |
| `scan_p0.py` | Source scanner rejecting `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`/unsafe constructs |
| `make_manifest.py` | Regenerates `MANIFEST.sha256` |
| `MANIFEST.sha256` | SHA-256 of every file in this record - `sha256sum -c MANIFEST.sha256` passes 100% |
| `verify_all.sh` | Chained re-verification driver (manifest check, P0 scan, build reminder) |
| `metadata.json` | Deposit metadata (title, keywords, license, related identifiers) |
| `LICENSE` | Apache License 2.0 |
| `NOTICE.txt` | Provenance notice (OEIS third-party content) |

## What is kernel-verified vs paper-level

Per the article's own accounting (Section "Formal verification",
Table `tab:lean`; machinery duplicated per multiplier, no
parametrized lemma):

**Kernel-verified** (all 53 modules green on external CI, axiom
audits at most `[propext, Classical.choice, Quot.sound]`):

- k=2, A069881: `A069881_even`, `A069881_overflow`,
  `succ_case_all5`, `A069881_image_odd`; repdigit iffs in
  `Repdigits_KP1.lean`. Axiom report `axioms-A069881.txt`.
- k=3, A083829/A083830: `A083829_even`, `A083829_prefix`,
  `A083829_digits`, `A083829_seven` (Israel P1-P4); image
  `A083830_digits` / re-export `A083830_alphabet`. Reports
  `axioms-A083829.txt`, `axioms-A083830.txt`.
- k=4, A083831/A083832: `A083831_even`, `A083831_digits`;
  `A083832_digits` / `A083832_alphabet`. Reports
  `axioms-A083831.txt`, `axioms-A083832.txt`.
- k=5, A083833/A083834: `A083833_C1`, `A083833_C2`
  (Branicky); image `A083834_C1`/`A083834_C2` and re-exports
  `A083834_alphabet`, `A083834_repunit`, `A083834_starts6_odd`.
  Reports `axioms-A083833.txt`, `axioms-A083834.txt` **plus**
  three-kernel seal replays `seal-A083833.txt`,
  `seal-A083834.txt` (the only modules with this extra level).
- k=6, A083835/A083836: the complete iff `A083835.A083835`
  (directions `all9_gives_pal`, `alt_gives_pal`),
  `A083835_even`, `A083835_digits`; image `A083836_digits`,
  `A083836_even`, `A083836_form` and re-exports. Reports
  `axioms-A083835.txt`, `axioms-A083836.txt`.
- zeros: `revW`, `okP`, `escapesIn`, `prefix_escapes`,
  `zero_of_escapes`, `no_wit_<k>` and `A083837_<k>_zero` for the
  21 indices (`A083837.lean`); 21 corollaries
  `A083838_<k>_zero` (`A083838.lean`). Reports
  `axioms-A083837.txt`, `axioms-A083838.txt`.
- spec closures: every `proven_A######` closes a capstone
  against the frozen spec; `Check_AntiVacuite_*` anchor on
  published terms and prove each class inhabited.
- alternating-class sufficiency: `alt_gives_pal` in each of
  `A069881.lean`, `A083829.lean`, `A083831.lean`,
  `A083833.lean`, `A083835.lean` certifies the converse
  direction for every k in {2,...,6} (kernel-verified since
  run 44922902734).

**Proved in the paper only** (stated as such in the article,
not claimed as kernel theorems): the k in {7,8,9} repdigit
families of Remark `rem:k1`, and the elementary k=1 remark.

**Outside the certified perimeter**: the nonzero displayed
values of A083837/A083838 (only the zero clause is proved, for
every candidate palindrome of any length); completeness of the
displayed lists of the eleven entries (empirical matter, not
claimed); the membership predicate ranges over m >= 1 digit
expansions without leading zero, so p = 0 is outside the
specification domain.

**Honesty notes on the audit files.**

- `axioms-A083835.txt`, `axioms-A083836.txt`,
  `axioms-A083837.txt`, `axioms-A083838.txt` consolidate the
  documented CI outcomes (runs 44892113988 / 44895777039) and
  the shipped harness modules; unlike the older per-suite
  reports they are not verbatim re-extractions of runner logs
  (the raw artifacts live on the CI mirror). They say so
  explicitly.
- The per-suite axiom reports reproduced from the earlier
  deposits mention an internal "sceau N5" stage in their
  closing paragraphs; the only three-kernel replay evidence
  shipped in this record is `seal-A083833.txt` /
  `seal-A083834.txt`. Treat the seal remark in the other
  `axioms-*.txt` as a historical pipeline note, not as shipped
  evidence here.
- `seal-A083833.txt` and `seal-A083834.txt` are the original
  seal reports verbatim; they reference the export archives
  `A083833-seal-exports.tar.zst` /
  `A083834-seal-exports.tar.zst`, which live in the original
  per-entry records and are not reproduced in this record.
  The reports remain the attestation that the three-kernel
  replay ran green (nanoda, con-leche, con-ron, exit 0).
- `anteriorite-*.md` files are verbatim copies of the
  per-entry audits; the four newest entries (A083835-38) have
  no separate prior-art audit file - their entries carry no
  published conjecture (Chandler's 2003 comment is the only
  claim addressed, and it is quoted in `oeis-verbatim.txt`).

## Reproducing the verification

```bash
# Lean / mathlib environment (elan, toolchain v4.35.0)
lake exe cache get
lake build            # all 53 modules are defaultTargets

# or a focused subset, e.g. the capstones:
lake build A069881 A083829 A083831 A083833 A083835 A083837

# Axiom audits (expect [propext, Classical.choice, Quot.sound] at
# most on every audited declaration):
lake env lean AxiomsReport_A083833.lean    # and likewise for the
                                         # other AxiomsReport_* modules

# Integrity of this record
sha256sum -c MANIFEST.sha256

# Source-surface audit (reject forbidden constructs)
python scan_p0.py *.lean

# or run the whole chain
./verify_all.sh
```

## Source normalization notice

The shipped `.lean` files are the canonical CI-built sources
with two mechanical, comment-only normalizations: U+2014/U+2013
dashes inside comments were replaced by `-`, and line endings
were normalized to LF. No token of any proof, statement or
specification was altered.

## References

- OEIS entries: https://oeis.org/A069881 ,
  https://oeis.org/A083829 ... https://oeis.org/A083838
- Companion article: `A083833-UNIFIE-paper.pdf` (this record)
- Previously deposited A083833 development:
  https://doi.org/10.5281/zenodo.24078012
