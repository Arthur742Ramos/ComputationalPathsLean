# Reference Check Report (sajl_main.tex)

## 1) Cite key ↔ bibitem consistency
- **Cite commands:** 18 instances, **13 unique keys**.
- **Bibitems:** 30 (all unique).
- **Missing bibitems:** **None** (every cite key resolves to a bibitem).
- **Orphaned bibitems (present but not cited):**
  - adams74, baez95, batanin98, brunerie16, burroni93, cohen18, eckmann62, hatcher02,
    hofmann98, lafont09, may99, metayer03, mltt84, ramos19, ravenel86, switzer75, whitehead78.
- **Duplicate bibitem keys:** none.

## 2) Log check for undefined refs/cites (sajl_main.log)
- **No undefined references/citations found.**
- Only a font warning appears: `LaTeX Font Warning: Font shape 'U/stmry/b/n' undefined`.

## 3) Web verification (10+ key references)
Sources: OpenAlex, Crossref, and the HoTT book site. Items below list **bibitem → web source → check**.

1. **ramos18** — *On the identity type as the type of computational paths* (Logic J. IGPL).
   - Web: OpenAlex record shows DOI **10.1093/jigpal/jzx015**, **publication year 2017**, Logic Journal of the IGPL.
     https://api.openalex.org/works?search=On%20the%20identity%20type%20as%20the%20type%20of%20computational%20paths&per-page=1
   - **Mismatch:** bibitem says **2018**, volume **26(4)**, pages **378–399**. OpenAlex/Crossref indicate 2017 (vol 25 issue 4, pp 562–584). Needs correction.

2. **lumsdaine10** — *Weak ω-categories from intensional type theory* (LMCS).
   - Web: OpenAlex shows **2010**, DOI **10.2168/lmcs-6(3:24)2010**, LMCS.
     https://api.openalex.org/works?search=Weak%20omega-categories%20from%20intensional%20type%20theory&per-page=1
   - **Match:** author/title/year/venue align; page range not confirmed by OpenAlex.

3. **vdberg11** — *Types are weak ω-groupoids* (PLMS).
   - Web: Crossref shows DOI **10.1112/plms/pdq026**, **Proc. London Math. Soc. 102(2):370–394 (2011)**.
     https://api.crossref.org/works?query.title=Types%20are%20weak%20omega-groupoids&rows=1
   - **Match:** author/title/year/venue/pages align with bibitem.

4. **hott13** — *Homotopy Type Theory: Univalent Foundations of Mathematics*.
   - Web: HoTT book page lists title and attribution to **The Univalent Foundations Program**, IAS.
     https://homotopytypetheory.org/book/
   - **Match:** title/authoring body/venue align (year 2013 consistent with first edition).

5. **bezem14** — *A model of type theory in cubical sets* (TYPES 2013 / LIPIcs).
   - Web: OpenAlex shows **2014**, DOI **10.4230/LIPIcs.TYPES.2013.107**, LIPIcs TYPES 2013.
     https://api.openalex.org/works?search=A%20model%20of%20type%20theory%20in%20cubical%20sets&per-page=1
   - **Match:** authors/title/year/venue align; bibitem omits explicit “LIPIcs” series name.

6. **cohen18** — *Cubical type theory: A constructive interpretation of the univalence axiom*.
   - Web: OpenAlex returns **TYPES 2015 (LIPIcs)** version, DOI **10.4230/LIPIcs.TYPES.2015.5**, year **2018**.
     https://api.openalex.org/works?search=Cubical%20type%20theory%20constructive%20interpretation%20univalence%20axiom&per-page=5
   - **Mismatch:** bibitem cites **Journal of Automated Reasoning 60(2):159–216 (2018)**. Web source shows a **conference** publication, not JAR. Verify which version should be cited.

7. **hofmann98** — *The groupoid interpretation of type theory*.
   - Web: Crossref shows **1998**, OUP book chapter in *Twenty Five Years of Constructive Type Theory*, DOI **10.1093/oso/9780198501275.003.0008**.
     https://api.crossref.org/works?query.title=The%20groupoid%20interpretation%20of%20type%20theory&rows=1
   - **Match:** author/title/venue/year align.

8. **favonia18** — *The Seifert–van Kampen Theorem in HoTT* (CSL 2016).
   - Web: OpenAlex shows **2016**, DOI **10.4230/LIPIcs.CSL.2016.22**, authors **Kuen-Bang Hou (Favonia)** & **Michael Shulman**.
     https://api.openalex.org/works?filter=title.search:Seifert%20van%20Kampen%20theorem%20in%20homotopy%20type%20theory&per-page=1
   - **Match:** details align; note key name is **favonia18** though publication year is **2016**.

9. **batanin98** — *Monoidal globular categories as a natural environment for the theory of weak n-categories*.
   - Web: OpenAlex shows **Advances in Mathematics 136(1):39–103 (1998)**, DOI **10.1006/aima.1998.1724**.
     https://api.openalex.org/works?filter=title.search:monoidal%20globular%20categories&per-page=1
   - **Match:** author/title/year/venue/pages align.

10. **ramos19** — *Explicit computational paths* (SAJL 2019).
   - Web: OpenAlex finds **arXiv 1609.05079 (2016)** preprint with same title and authors.
     https://api.openalex.org/works?filter=title.search:explicit%20computational%20paths&per-page=1
   - **Mismatch / needs confirmation:** bibitem cites **SAJL 5(2):1–52, 2019**. Web data only confirms the **2016 preprint**, not the journal version.

11. **dqor16** — *Propositional equality, identity types, and direct computational paths* (SAJL 2016).
   - Web: OpenAlex finds **arXiv 1107.1901 (2011)** with authors **de Queiroz** and **de Oliveira** only.
     https://api.openalex.org/works?search=Propositional%20equality%20identity%20types%20and%20direct%20computational%20paths&per-page=1
   - **Mismatch / needs confirmation:** bibitem lists **2016 SAJL** and includes **Ramos** as coauthor. Journal metadata should be confirmed from SAJL.

12. **brunerie16** — *On the Homotopy Groups of Spheres in HoTT* (PhD thesis).
   - Web: OpenAlex shows **2016 arXiv 1606.05916** preprint by **Guillaume Brunerie** with same title.
     https://api.openalex.org/works?filter=title.search:Homotopy%20Groups%20of%20Spheres%20in%20Homotopy%20Type%20Theory&per-page=1
   - **Partial match:** confirms title/author/year, but does **not** validate the thesis institution; verify the thesis metadata separately.

## 4) Newly added references (format + citation status)
- **hofmann98**: Format aligns with Crossref; **not cited** in text (orphan).
- **favonia18**: Format aligns with OpenAlex; **cited** once (line ~2689).
- **brunerie16**: Format plausible; **not cited** in text (orphan).
- **batanin98**: Format aligns with OpenAlex; **not cited** in text (orphan).

## 5) Formatting consistency observations
- **LIPIcs series naming is inconsistent**: `bezem14` lists “volume 26” but does not name LIPIcs, while `favonia18` explicitly names “Leibniz International Proceedings in Informatics”.
- **Year mismatch in keys**: `favonia18` key suggests 2018 but the publication year is **2016**.
- **Possible venue mismatches**:
  - `cohen18` is listed as **JAR 60(2):159–216 (2018)**, but OpenAlex shows the **TYPES 2015 (LIPIcs)** version for that title.
  - `ramos18`, `ramos19`, and `dqor16` show preprint metadata (OpenAlex) that conflict with current journal-year/page data in the bibitems.

## 6) Missing or under-cited references (requested categories)
- **HoTT book**: Present and cited (`hott13`).
- **Algebraic topology**: Core texts (Hatcher, May, Switzer, Whitehead, Adams, Ravenel) exist in bibliography but are **not cited** in the text.
- **Lean formalization papers**: **Missing.** Consider adding Lean 4 references (e.g., *The Lean 4 Theorem Prover and Programming Language*, *Theorem Proving in Lean*), and/or Lean HoTT-related formalization papers.
- **de Queiroz prior work**: Early LND/Equality papers (e.g., de Queiroz & Gabbay LSFA 2011; “Equality in Labelled Deductive Systems”) are **not present** in the bibliography.

## 7) URLs / DOIs
- **No URLs/DOIs are included** in the BibTeX entries in `sajl_main.tex` (confirmed by `rg https?://` and scan of bibliography). Therefore **no broken-link checks** could be performed.
- Consider adding DOIs or URLs for key journal entries (e.g., `vdberg11`, `lumsdaine10`, `cohen18`, `batanin98`) to improve traceability.

---
If you want, I can draft corrected bibitems (with DOIs/series info) and/or prune orphans to align the bibliography with in-text citations.
