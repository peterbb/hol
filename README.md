This is a proof assistant for intuitionistic higher order logic. 

# Core logic
## Types and Terms
A signature, Sigma, is on the form:

    Sigma ::= . | Sigma, a type | Sigma, c : A
    
where `a` is a type constant, `c` a term constant, and `A` a type. Types are
defined as:

    A, B ::= a | A -> B
    
A type is well-formed if all then type constants that occur in it is declared in the signature.
Terms are defined as

    M, N ::= \x.M | H S
    H ::= x | c
    S ::= . | M S
    
The judgments `Sigma; Gamma |- M : A` and `Sigma; Gamma [A] |- S : B` defines the typing relation
of terms.  `Gamma` is a context, defined as:

    Gamma ::= . | Gamma, x : A
    
And the rules for typing is:

      Sigma; Gamma, x:A |- M : B
    -------------------------------
      Sigma; Gamma |-\x.M : A -> B
     
      x:A in Gamma     Sigma; Gamma [A] |- S : B
    -----------------------------------------------
          Sigma; Gamma |- x S : B
          
      c:A in Sigma     Sigma; Gamma [A] |- S : B
    -----------------------------------------------
          Sigma; Gamma |- c S : B
          
    ----------------------------
      Sigma; Gamma [A]|- . : A
      
      Sigma; Gamma |- M : A     Sigma; Gamma [B] |- S : C
    ------------------------------------------------------------
             Sigma; Gamma [A -> B] |- M S : C
             
## Propositions and Proofs
We make the initial signature contain the following type
and term constants:

* `o type`
* `true, false : o`
* `and, or, iml : o -> o -> o`
* `all_A, ex_A : (A -> o) -> o`

Notice that there is strictly speaking an "infinite number" of constants in the initial signature, as we have `all_A` and `ex_A` for each type `A`.

We have a single judgment `Sigma; Gamma; Delta |- M`. Here it is assumed that `Sigma; Gamma |- M : o`. Furthermore,
`Delta` is on the form `h_0:M_0, ..., h_n:M_n` where `h_i` a name for an assumption and `Sigma; Gamma |- M_i : o`.
The assumptions `Delta` is unordered, and a name occures only once.

    --------------------------- assumption h
      Gamma; Delta, h:M |- M
      
        Gamma; Delta |- M    Gamma; h:M, Delta |- N
      ------------------------------------------------- cut M h
             Gamma; Delta |- N
