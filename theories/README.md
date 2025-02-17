# RichWasm Formalization 

## Compile

To compile the Coq code you will need Coq 8.13.2. Then simply type:

	make Coq.Makefile
	make


## Directory Structure

- `tactics.v` `EnsembleUtil.v` `functions.v` `list_util.v` `map_util.v`: Generic helper libraries
- `term.v`: Syntax of RichWasm
- `debruijn.v`: Generic definitions of substitutions and related operations for DeBruijn indices
- `subst.v`: Instantiation of the generic DeBruijn operations for the RichWasm language
- `memory.v`: Definition of the memory model as a Coq module
- `locations.v`: Definition of reachability and specification of GC
- `reduction.v`: Definition of the reduction relation
- `typing.v`: Definitions of the various typing judgments
- `splitting.v`: Formalization of the disjoint union operation of the linear memory typing
- `surface.v`: Formalization of well-formedness predicates for surface source programs
- `typing_util.v`: Miscellaneous lemmas for the typing judgments
- `misc_util.v`: Miscellaneous lemmas about substitutions, mostly related to preservation of typing
- `hti_subst_indices.v`: Lemmas stating that instruction typing is preserved under valid substitutions
- `progress.v`: Progress proof
- `preservation.v`: Preservation proof of instruction typing for the reduction rules that do no involve the heap
- `preservation_full.v`: Preservation proof of instruction typing for the reduction rules that involve the heap
- `preservation_GC.v`: Preservation proof of instruction typing for the GC rule of the reduction relation
- `safety.v`: Top-level theorem for type safety

## Definitions and Theorems

For each definition and theorem that appears in the paper, we give a pointer to the corresponding location in the code.


### Section 2

- (Pre)types (pg 5, fig. 2): `term.v` lines 71-85
- Values (pg 5, fig. 2): `term.v` line 121
- Heap values (pg 5, fig. 2): `term.v` line 133
- Instructions (pg 5, fig. 2): `term.v` line 216
- Functions (pg 5, fig. 2): `term.v` line 297
- Globals (pg 5, fig. 2): `term.v` line 306
- Modules (pg 5, fig. 2): `term.v` line 311

### Section 3

The reduction relation is split across few relations each one representing reduction steps

- Reduction steps that do not involve the heap:  `Reduce_simple`, file `reduction.v` line 211
- Reduction steps that involve the heap: `Reduce_full`, file `reduction.v` line 451
- Reduction relation with congruence rules: `Reduce`, file `reduction.v` line 627
- Garbage-collection step: `GC_step`, file `reduction.v` line 659
- Top-level reduction relation: `Reduce_GC`, file `reduction.v` line 682

### Section 4

- Local environment: `Local_Ctx`, file `typing.v` line 447
- Function environment: `Function_Ctx`, file `typing.v` line 449
- Module environment: `Module_Ctx`, file `typing.v` line 441
- Store typing: `StoreTyping`, file `typing.v` line 702
- Value typing: `HasTypeValue`, file `typing.v` line 1522
- Instruction typing: `HasTypeInstruction`, file `typing.v` line 1880
- Store typing: `HasTypeStore`, file `typing.v` line 3738
- Configuration typing: `HasTypeConfig`, file `typing.v` line 3747

<!--- useless Markdown comment to separate the lists --->
- Top-level progress theorem: `Progress`, file `progress.v` line 2618
- Top-level preservation theorem: `Preservation`, file `safety.v` line 2800

We also prove a top-level soundness theorem (not shown in the paper): `Soundness`, file `safety.v` line 2928

## Note about Paper

In the RichWasm paper, it says

 > It contains one remaining admitted lemma related to substitution (among many others that we have fully proved).

At the time of submitting this artifact for the RichWasm paper, there was an admitted lemma in the file `hti_subst_indices.v`, named `HasTypeInstruction_subst_index`. However, this lemma has now been proven, so there are no longer any remaining admits in this artifact.

For those curious, the `HasTypeInstruction_subst_index` lemma says that for well-typed instructions `S; M; F; L |- es : tau_1* -> tau_2* | L'` and a concrete instantiation `I` of a kind variable `rho` where `I` satisfies the constraints of `rho`, the typing judgement still holds after substituting `rho` with `I`, that is,
```
S; M; F[I/rho]; L[I/rho] |- es[I/rho] : tau_1[I/rho]* -> tau_2[I/rho]* | L'[I/rho].
```

Note that, between submitting the artifact and proving this lemma, we added an extra assumption to `QualifyTyp`: `forall n, p <> TVar n`. This states the pretype in the input to `QualifyTyp` must not be a type variable. This restriction is necessary because type variables can become capabilities or references after substitution.
