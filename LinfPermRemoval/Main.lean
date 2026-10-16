/-
Formalization of V. H. Le, R. Shi, F. Wei, "$L_\infty$ Permutation Removal Lemma"
(unpublished manuscript). Not part of Mathlib.
-/
import LinfPermRemoval.MainTheorems

/-!
# Index: paper results and their Lean names

Numbering is taken from the compiled `.aux` of the source. Every numbered environment of the
paper has a row; the unnumbered Remarks, the figures and the introduction's prose are out of
scope.

| Result | Lean |
|---|---|
| Theorem 1.1 | `thm_1_1_lower`, `thm_1_1_upper` |
| Theorem 1.2 | `thm_1_2` |
| Definition 2.1 | `IsAssoc`, `Represents`, `IsPermPointSet`, `canon` |
| Definition 2.2 | `rhoInf`, `maxDisp` |
| Definition 2.3 | `IsFar`, `IsFarFromFree` |
| Fact 2.4 | `fact_2_4` |
| Lemma 3.1 | `lemma_3_1` |
| Claim 3.2 | `claim_3_2` |
| Construction 3.3 | `con_3_3` |
| Claim 3.4 | `claim_3_4` |
| Claim 3.5 | `claim_3_5` |
| Construction 3.6 | `con_3_6`, `sort36`, `key36`, `regionU`, `regionL`, `regionR` |
| Fact 3.7 | `fact_3_7` |
| Fact 3.8 | `fact_3_8` |
| Claim 3.9 | `claim_3_9` |
| Construction 3.10 | `con_3_10` |
| Construction 3.11 | `con_3_11`, `val311` |
| Theorem 4.1 | `thm_4_1`, `GeomConclusion` |
| Definition 4.2 | `PosSlope`, `NegSlope` |
| Claim 4.3 | `claim_4_3_1`, `claim_4_3_2`, `claim_4_3_3`, `claim_4_3_4` |
| Construction 4.4 | `P44`, `PM44` |
| Lemma 4.5 | `lemma_4_5` |
| Claim 4.6 | `claim_4_6` |
| Claim 4.7 | `claim_4_7` |
| Claim 4.8 | `claim_4_8`, `S45` |
| Construction 4.9 | `P49`, `PM49` |
| Lemma 4.10 | `lemma_4_10` |
| Claim 4.11 | `claim_4_11` |
| Construction 4.12 | `PM412`, `PB412`, `PR412` |
| Lemma 4.13 | `lemma_4_13` |
| Claim 4.14 | `claim_4_14` |
| Construction 4.15 | `PL415`, `PU415`, `PB415`, `PR415`, `D415` |
| Lemma 4.16 | `lemma_4_16` |
| Claim 4.17 | `claim_4_17` |
| Claim 4.18 | `claim_4_18` |
| Construction 4.19 | `IL419`, `IR419`, `IB419`, `IU419`, `PL419`, `PR419`, `PB419`, `PU419`, `D419` |
| Lemma 4.20 | `lemma_4_20` |
| Claim 4.21 | `claim_4_21` |
| Corollary 4.22 | `cor_4_22` |
| Claim 4.23 | `claim_4_23` |
| Claim 4.24 | `claim_4_24` |
| Claim 4.25 | `claim_4_25` |
| Claim 4.26 | `claim_4_26` |
| Corollary 4.27 | `cor_4_27` |
| Construction 4.28 | `Pa428`, `D428` |
| Lemma 4.29 | `lemma_4_29` |
| Claim 4.30 | `claim_4_30` |
| Corollary 4.31 | `cor_4_31` |
| Claim 4.32 | `claim_4_32` |
| Claim 4.33 | `claim_4_33` |
| Claim 4.34 | `claim_4_34`, `UD`, `BD` |
| Corollary 4.35 | `cor_4_35` |
| Claim 4.36 | `claim_4_36` |
| Corollary 4.37 | `cor_4_37` |
| Corollary 4.38 | `cor_4_38`, `LD`, `RD` |
| Construction 4.39 | `PH439`, `PV439`, `D439` |
| Lemma 4.40 | `lemma_4_40`, `Hyp440` |
| Claim 4.41 | `claim_4_41` |
| Corollary 4.42 | `cor_4_42` |
| Claim 4.43 | `claim_4_43` |
| Claim 4.44 | `claim_4_44` |
| Claim 4.45 | `claim_4_45` |
| Claim 4.46 | `claim_4_46` |
| Claim 4.47 | `claim_4_47`, `SigBR` |
| Corollary 4.48 | `cor_4_48` |
| Claim 4.49 | `claim_4_49` |
| Claim 4.50 | `claim_4_50` |
-/
