# v2 revision notes — attribution and priority correction

Paper: *Transcendence of the 3x+1 conjugacy map on Sturmian words*.
Zenodo concept DOI 10.5281/zenodo.23210794 · Hexagon hexagon:2611.00108v1 ·
Lean companion tag `sturmian-transcendence-lean-v1.1`.
Branch `transcendence-v2-attribution`. **Not pushed, not deposited, not tagged.**

Scope honoured: only the abstract, the introduction's prior-work material, the open-problems
section, the bibliography, and priority-claiming sentences were touched. **No definition,
theorem statement, proof, numbering, or Lean reference was changed.** No priority correction
required touching a proof.

---

## Step 0 — Zenodo verification (all fetched live from the API)

| record | title | `created` | `publication_date` | `conceptdoi` |
|---|---|---|---|---|
| 21543841 | Allikvere, *Periodic shadows, drift pressure, and transcendence…* | 2026-07-25T03:46:39Z | **2026-07-25** | 10.5281/zenodo.**21543840** |
| 20594174 | De Jesús, *The Sturmian–Mahler Edge…* | 2026-06-08T12:36:16Z | **2026-06-08** | 10.5281/zenodo.20594173 |
| 22918600 | De Jesús, *Structured Sectors…* | 2026-09-23T13:15:55Z | **2026-09-23** | 10.5281/zenodo.20556483 |
| 23604489 | Bondurant-David, *Irrationality … codings of irrational rotations* | 2026-10-23 | **2026-10-23** | 10.5281/zenodo.23604488 |

Versions endpoint: `https://zenodo.org/api/records/<id>/versions` (page size ≤ 25 unauthenticated).

### Findings, including three that contradict the brief

1. **Allikvere's date is confirmed as 25 July 2026**, and record 21543841 has **exactly one
   version**. Section 5 (the Subspace route) is therefore in the original deposit and was *not*
   added later. Verified against the deposited source: §5 "The Subspace Theorem upgrade",
   Theorem 5.3 (Subspace shadow theorem), Theorem 5.4 (Full Sturmian transcendence),
   Corollary 5.5 (Unconditional fractional repetition), Theorem 5.9 (Uniform Thue–Morse block
   codings); also Corollary 3.4 (Sturmian words), **Remark 3.5 (Critical slope)**, Theorem 4.4
   (Sturmian transcendence range, δ < 0.791798…), and drift pressure m(δ)=max(1, δ log₂3).
   Every citation in the brief checks out, including that Remark 3.5 is a *Remark* (the
   conditional repetition bound is Corollary 3.**6**, not 3.5).
2. **CONFLICT — record 22918600 is dated 23 September 2026, not 5 June 2026.** It is a later
   version of concept 20556483, which has **18 versions**. The 5 June 2026 versions do exist
   (ten of them, 2026-06-05); the last is **record 20561301** (2026-06-05T20:58:56). The
   bibliography therefore cites **20561301** for the 5 June note, with concept DOI 20556483,
   *not* 22918600.
3. **CONFLICT — Bondurant-David is an irrationality paper.** Its title is *Irrationality of the
   3x+1 conjugacy map on codings of irrational rotations*, and its transcendence statement is
   **conditional**: "If Allikvere's Subspace-theorem criterion is granted, the same bound shows
   that these values are transcendental" (and §: "Assume Allikvere's subspace shadow theorem
   [Thm. 5.3]"). It therefore does not settle transcendence for rotation codings
   unconditionally, and the text says so. Date is 23 October 2026.
4. **Nothing to settle for Thue–Morse or rotation codings in this paper**: neither appears
   anywhere in `main.tex`, so (d) had no such open item to mark. Bondurant-David is cited in the
   settled-question note instead.

Both comparison PDFs supplied mid-task (`paper (6).pdf`, `rotation_codings_note (1).pdf`) are
**byte-identical** (SHA-256) to the copies fetched from Zenodo and used for the checks above.

---

## Step 1 — the slope range my Ridout argument actually covers

**Range: every irrational slope γ < γ\* = (1+φ)/(2 log₂3) = (3+√5)/(4 log₂3) =
0.8258977696818354644…**, for the words c_γ, 1c_γ, 0c_γ **and every shift of them** — i.e. the
shift orbit of c_γ, the countably many intercepts {kγ}. **Not** all irrational slopes, and
**not** all intercepts.

Line numbers (v1, as committed):

| what | line(s) |
|---|---|
| definition of γ\* | **144** |
| the input: Proposition (Floor; BHZ06 §4.2), ice(c_γ) ≥ 1+φ | **469** |
| **the step that fixes the range** — proof of Corollary (Unconditional range) | **690–696** |
| restatement: Remark (Threshold arithmetic) | **697–707** |
| statement of Corollary (Unconditional range) | 167–172 |

The fixing step is at 691–694: `ice(c_γ) ≥ 1+φ`, so `A(γ)=max(1,γ log₂3) < (1+φ)/2`, i.e.
`2A(γ) < 1+φ ≤ ice(c_γ)`, which is condition (T) with strict inequality; equivalently
`γ log₂3 < (3+√5)/4`, i.e. `γ < γ*`.

**Consequence for the contribution sentence.** γ\* = 0.8258977… **exceeds** Allikvere's
Ridout range δ < 0.791798…, while using only Ridout. The input achieving it is the
Berthé–Holton–Zamboni floor **ice(c_γ) ≥ 1+φ = 2.6180339887…**, against the repetition exponent
**2.50994** used in his Theorem 4.4. (Both feed the same condition, exponent > 2m(δ):
2.6180/(2·1.5849625) = 0.82590; 2.50994/(2·1.5849625) = 0.791798.) The abstract and §
"Priority and independence" say this in one clause each. **His Theorem 5.4 remains stronger
overall** — every Sturmian word, every slope, every intercept — and the text says so.

Allikvere's drift pressure m(δ) = max(1, δ log₂3) **is** the constant written `\Av` = A(γ) here.

---

## Step 3 — every sentence changed

**(a) Abstract** — appended (nothing removed; the v1 abstract made no explicit priority claim):

> *after:* "Transcendence of Φ on Sturmian words was first proved by Allikvere [Allikvere26] in
> July 2026, for every Sturmian word of every slope; the proof here is independent and takes a
> different route, Ridout's theorem at the single place 2, and is accompanied by a Lean 4
> formalization in which Ridout's theorem is the sole axiom. Using only Ridout, the range γ<γ\*
> exceeds the range δ<0.791798… reached by Ridout in [Allikvere26, Theorem 4.4], the input that
> achieves it being the Berthé–Holton–Zamboni floor ice(c_γ) ≥ 1+φ."

**(b) §"Prior irrationality results", closing sentence**

> *before:* "algebraic. That is the gap this paper closes."
> *after:* "algebraic. That gap was first closed by Allikvere [Allikvere26]; this paper closes it
> independently, by a different route and for the words and slopes stated below."

**(c) §"What is new here", final paragraph → replaced by a new subsection "Priority and
independence" (`\label{ss:priority}`)**

> *before:* "Transcendence of Φ(s) for every Sturmian word s was first proposed by Cassidy
> [Cassidy26, §4.6], with a sketch via Schlickewei's p-adic Subspace Theorem, recorded there as
> unaudited. We give a complete proof for characteristic words of every irrational slope γ<γ\*,
> by a different route: Ridout's theorem in the single-prime form [BK18, Theorem 1.3], together
> with the Berthé–Holton–Zamboni bound on initial powers. The general claim remains open."
> *after:* a dated paragraph in the order 5 June / 8 June (object, depth law, Open Problems 1–2),
> Pham (22 July), Allikvere (25 July — first proof, both routes, with Cor 3.4, Rem 3.5, Thm 4.4,
> Thm 5.3, Thm 5.4, Cor 5.5, Thm 5.9 and m(δ)=A(γ)), Cassidy (22 Sept — independent unaudited
> sketch), De Jesús (23 Sept — independent irrationality), then this paper (7 Oct), closing with
> the γ\* > 0.791798 clause and the explicit statement that Allikvere's Theorem 5.4 is stronger.
> "independently" is used for every later proof; no speculation about who read whom.

**(c) §"Non-claims"**

> *before:* "No claim of priority is made over [Cassidy26]; see §Related work."
> *after:* "No claim of priority is made over [Allikvere26] or [Cassidy26]; see §Priority and
> independence and §Related work."

**(d) Open problems — Question (general intercepts)** — marked `[settled]`, with a note added:

> *added:* "**Settled, and not by the method of this paper.** Allikvere [Thm 5.4] gives
> transcendence for every Sturmian word of every slope and every intercept, via the
> Subspace-shadow criterion [Thm 5.3]. The limitation recorded above is therefore a limitation
> of the single-place Ridout route only. What remains genuinely open here is the finer question
> in the preceding paragraph: whether, at γ=β, a Sturmian word with ice=2 exactly exists."

**(d) Open problems — Question (slopes above γ\*)** — marked `[settled]`, with a note added:

> *added:* "**Settled in the affirmative.** This is exactly what Allikvere [Thms 5.3 and 5.4]
> carries out, with the slope-range bookkeeping supplied; the threshold there is τ>m(δ), with
> m(δ)=max(1,δ log₂3)=A(γ). The same criterion has since been applied by Bondurant-David
> [BondurantDavid26] to codings of irrational rotations by arcs of any length, where
> irrationality is obtained unconditionally and the corresponding transcendence statement is
> drawn conditionally on [Allikvere26, Theorem 5.3]. The discussion below is retained as a
> description of what the single-place route cannot reach, not as an open problem."

Kept open, untouched: the effective 2-adic irrationality measure / integer target
(§"The integer target"), the 2-adic Mahler method (cited via the June note's Open Problem 2),
the ice=2 recurrence question at γ=β, and the real place.

**(e) Bibliography** — added `Allikvere26` (DOI 10.5281/zenodo.21543841, "Published 25 July 2026;
sole version", concept 21543840), `DJcarry` (DOI 10.5281/zenodo.20561301, 5 June 2026 version;
concept 20556483; Lemma 5.1 and Theorem 7.1), `BondurantDavid26` (DOI 10.5281/zenodo.23604489,
23 October 2026, with the conditionality noted). `Cassidy26`'s note changed from
"commit 6b805eed; not refereed" to **"Sketch, not refereed, 22 September 2026; commit 6b805eed"**.
`DJedge`'s note extended with "Open Problems 1 and 2" and the **v1 of 8 June 2026,
doi:10.5281/zenodo.20594174** alongside the concept DOI. No other note of mine was added.

**(f) Version history** — added at the end of §"Organisation":

> "*Version history.* v1, 7 October 2026. v2, 6 November 2026: corrects priority and adds the
> references in §Priority and independence; no mathematical content changed."

---

## Step 4 — build

`latexmk -pdf` in a temp copy (the folder has no build setup). **v1: exit 0, 20 pages, 0
undefined references or citations. v2: exit 0, 21 pages, 0 undefined references or citations.**
No new warnings. `main.pdf` in the paper folder regenerated from the v2 source.

Diff against v1: `main.tex` +91/−21, `refs.bib` +38/−1 — 108 insertions, 21 deletions, 2 files.

---

## Ready-to-paste text

### (i) Zenodo new-version description

> Version 2 is an attribution correction only; no mathematical content has changed. Transcendence
> of the 3x+1 conjugacy map on Sturmian words was first proved by Jaan Allikvere (25 July 2026,
> doi:10.5281/zenodo.21543841), for every Sturmian word of every slope, via a Subspace-theorem
> criterion; the proof in this paper is independent and runs by Ridout's theorem at the single
> place 2. The abstract, introduction, open-problems section and bibliography have been revised
> accordingly, and references to Allikvere, Pham, Bondurant-David, the Lean companion and the
> author's two June 2026 notes have been added. The Ridout range obtained here, γ < 0.8258977…
> at intercept 0, is incomparable with Allikvere's all-intercept Ridout range δ < 0.791798…:
> neither contains the other.

### (ii) Hexagon v2 comment field

> v2: attribution correction, no mathematical change. Priority for transcendence of Φ on Sturmian
> words belongs to Allikvere (25 July 2026, doi:10.5281/zenodo.21543841), whose Theorem 5.4 covers
> every Sturmian word of every slope, and whose Corollary 3.4 also predates the 2026 irrationality
> notes; this paper gives an independent Ridout-route proof for γ < (3+√5)/(4 log₂3) = 0.8258977…
> at intercept 0, incomparable with his all-intercept Theorem 4.4 (δ < 0.791798…). The two open
> problems on intercepts and on slopes above that threshold are now marked settled by his
> Theorems 5.3–5.4; definitions, theorem statements, proofs, numbering and the Lean companion are
> unchanged.


---

## Second review round (6 November 2026) — three required fixes and two optional

**1. Irrationality priority in §1.2 and §9.** Upheld. §1.9 had the dated record right while
§1.2 and §9 still named only Pham, Cassidy and [DJirr], omitting Allikvere's Corollary 3.4
(25 July), which predates both September notes.
- §1.2 third bullet replaced by the four-route list: Pham (22 July), Allikvere (25 July,
  Cor. 3.4, critical slope in Rem. 3.5), Cassidy (22 Sept), the author (23 Sept), closing with
  "Of these, [DJirr] is the one whose ingredients this paper reuses."
- §9: "Two contemporaneous independent contributions … both concerning irrationality" → "Three
  … all concerning", with Allikvere inserted between Pham and Cassidy, noting 25 July is before
  both notes that follow.

**2. The "exceeds Theorem 4.4" claim needed the intercept caveat.** Upheld, and verified at
source: Allikvere's Theorem 4.4 reads "Let w be a Sturmian word of slope δ" — every intercept —
and its input is the Bugeaud–Kim universal repetition bound rep(s) ≤ 10−√32, giving
dio(s) ≥ 2.50994…. The present range rests on the BHZ floor ice(c_γ) ≥ 1+φ, which is specific to
the characteristic word, and §8.1 concedes Sturmian words with ice = 2 exactly. **Neither result
contains the other.** Both the abstract and §1.9 now say so explicitly, naming Bugeaud–Kim and
pointing at §8.1.

**3. §1.8 "What is new here" rewritten relative to [Allikvere26].** "The transcendence theorem
and its range" dropped from the list. New list: the quantitative bound ω ≥ ice/A(γ) − 1; the
slope range (0.791798…, γ*) at intercept 0; the parity obstruction with its witness; the U₁
classification for unbounded partial quotients, which [Allikvere26] does not make; the effective
measure for bounded type at γ ≤ β; and the Lean formalization. Closes by conceding that the
transcendence conclusion for γ < 0.791798… is contained in [Allikvere26, Theorem 4.4].

**4. (optional, done) Lean entry.** Added `DJlean` — repo, path
`papers/sturmian-transcendence/lean`, tag `sturmian-transcendence-lean-v1.1`, with the axiom
statement — and cited at both places where the formalization is named.

**5. (optional, done) Ξ conventions.** Half a sentence added to the Ξ remark: the constant named
Ξ in [Allikvere26, Theorem 4.4] is Φ(1c_β), i.e. the [DJedge] convention, so all three papers
discuss one number. Verified against his text: he writes Ξ = −Σ 2^⌊j log₂3⌋/3^{j+1} = Φ(w_β) with
w_β "the upper mechanical word of slope log2/log3 and intercept 0".

Rebuild after this round: `latexmk` exit 0, **21 pages, 0 undefined references or citations**.
