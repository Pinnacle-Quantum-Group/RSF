# Cross-Reference: Lemma Derivation Mapping

The complete lemma derivation mapping for the PQG framework is maintained in:

**Repository:** [pinnacle-quantum-group/rssn](https://github.com/pinnacle-quantum-group/rssn)
**Branch:** `claude/lemma-derivation-mapping-WrwCv`

## RSF-Specific Results

| Theorem | Status | Key Lemmas |
|---------|--------|------------|
| RSF T1 (Cardinality Transcendence) | **TIGHT** | L2.1 density non-collapse, L2.2 no hidden hierarchy |
| RSF T2 (Continuum Resolution) | **TIGHT** | L4.1 spectrum dense, L4.2 CH dissolution |
| RSF T3 (Russell's Transcendence) | **TIGHT** | Axiom 7 direct |
| RSF T5 (Recursive Foundation) | **TIGHT (ANCHOR)** | Axiom 7 direct |

## RSF Axiom 9 (Density Convergence) -- Critical Cross-Framework Role

Axiom 9 is novel to RSF and supplies the missing Cauchy condition for RSSN T1 convergence via Bridge Lemma B.1. This is the highest-leverage axiom in the entire framework.

## Test Suite

RSF lemma tests: `rssn/tests/test_rsf_lemmas.py`
Gap analysis (including Con(ZFC) mapping): `rssn/tests/test_gap_analysis.py`
