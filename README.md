By: Jonathan Wilson
# Translating Away Effects in Call by Push Value
Side effects in programming make code harder to reason about. They allow for functions to read or modify state in an unintuitive, unexpected, and often unintended way. They also cause strange coupling between seemingly unrelated pieces of code such as the left part of a tuple affecting some computation in the right half. Lastly, proofs of correctness for code with side effects are often much more difficult as witnessed by our class's extensive talks on quantifying over memory cells.
Because dealing with effects is difficult, there is often a push (especially from proponents of both concurrent and functional code) to write pure code. These discussions are often centered around the idea that pure code is a safer and more correct subset of impure code. However, in any language with function and product types, the side effects of state can be embedded into the language. In other words, state is merely a mode of use for most programming languages.
To illustrate that state can be implemented with the same statics and dynamics as a pure language, I chose to implement a stateful language in a pure one. For this language, I chose Call-by-Push–Value as it has a small set of statics and dynamics, is readily available encoded in Agda for our PSet 8 and 9, and has a very expressive type system that allows for type level constraints that neatly capture effects.
## Background:
The oldest literature that inspired my work was from Moggi 91 and Wadler 95 (See figure 1 and 2). These works both model state as something along the lines of T A = S → (A x S). i.e. every computation takes in the global state S then returns what it would along with the new state. A great summary of this is available on YouTube from a talk given by Max S. New (figure 3).
The theory underlying this project is completely described by Paul Levy in The Call by Push Value Guide in section 5.4 (2022). The key insight is that since U F forms a monad, we want U F (A) = S → A x S. This project ended up encoding this the same way Levy did, with F A = A x S and U X = S → X. The intuitive reason for splitting it up like this instead of all of the pieces on the F or the U is that computations require the state in order to run. This means in order to have a computation embedded within values for the U type, we need to take in some additional state information. In order to run a computation as done by F A, we need to provide the value of the state after the computation is finished. 
There are two other encodings of state that satisfy our monad equation, but are bad encodings in Call by Push Value. If we were to put the entire monad onto the values, i.e. F A = S → (A x S), our computations would lose access to the state structure. All effects would be local to an individual return expression and a Bind would not be able to transfer effects between the states. The other bad encoding is to put the entire monad on the computations, i.e. U X = S → (A x S). While this encoding allows the computations to read and modify the state, it restricts our ability to read or copy the state. Since pairs of computations in Call by Push Value can only be used once, the program can only use either the result of the computation or the new state. For our set function for example, we want both the result of the computation and the new state. This also makes sense with our interpretation of values as the state of our program. If we want the state to last longer than simply the moment it is computed, we want to extend our value types with the type S.
## Work
The main takeaway from this is the simplicity and brevity with which state can be described in Call by Push Value. All of the control flow is the same as in the original Call by Push Value. The only extension to the state is the one cell needed for the state. In the non-effectful operations, the state is simply passed forward unchanged. The exception is the bind operation which needs to pass the effects computed from the F to the function. All of the Beta, Eta, and set/get laws are only a few lines giving the user 
This work shows an implementation of CBPV with a single global store accessible through get and set computations. As in the PSet 9 assignment, our CBPV-State has all of the same theorems. Most of the theorems were straightforward only requiring a few beta and eta reductions to prove. The exception is the additional bind-bind law. The trouble arises in that the state must be split then reused later after moving through the bind. The solution to this is to come up with a bind-split law that allows us to move the split operation throughout a bind.
In order to prove that split commutes with bind and thus binding is associative, we need to reason about values of product type. I believe that the only way to handle this is with a canonical forms lemma. We need to know that splitting a value before or after a bind / F computation does not affect the computation. The canonical forms lemma solves this as we can substitute in the value with its pieces. An equally difficult, but possibly viable solution is to introduce projections 1 and 2 for splitting pairs of values and expand the pair into its eta form. This likewise allows us to reason about the pieces. 
## Further readings
There are three places further I would like to take these proofs. The first is to create a representation independence proof between the effectful and pure CBPV using my translation as a guide. This would look like an isomorphism proof between the two. This would be very easy to do by merely stating that the resulting programs must be the same between the two. An example of this sort of correspondence is already included for the fib function.
The second and next most difficult area for future study is adding dynamic stores through symbol generation. While dynamic stores could be encoded by making the state one large mapping function that takes in a symbol, it is interesting to annotate and prove charastics about the scope for generated symbols. Levy has some notes on getting started with this as in Figure 4. 
The last area of study I would like to examine is comparing memory safety proofs on the pure Call by Push Value. I believe that it will be much easier to reason about the store in the monadic form rather than the language addition form. This is because the structure of the language itself will help guide the proof. Research on linear logics like Rust have a wealth of literature on accounting for memory safety. These are somewhat orthogonal to Call by Push Value though and do not leverage the full power of Agda.
An interesting extension to this Agda based encoding would be using dependent type theory in the language to prove safety. Hongwei Xi and Dengping Zhu have a lot of work on proving memory safety in Dependent languages with their Dependent ML and now ATS (Applied Type System). These might serve as interesting HOT Comp style projects where a subset of these dependent languages are encoded in a theorem prover and proven safe using transformations like the store passing one in this project.


## Appendix

Figure 1: Moggi 91. Definition of translation for adding state. The power of S is related to the arrow type.

Figure 2: Wadler 95. Here we see a more concrete example of a translation of the computations to account for state.

Figure 3: Max S. New. HOPE ‘22 Conference. Relevant slide on state from the talk “Relative Monads in CBPV for Stack-based Effects.”

Figure 4: Paul Levy Guide to Call By Push Value. Section 4.6.
Citations in Order of Appearance
Reading on transforming effects into pure computation without Call by Push Value
https://www.cs.cmu.edu/~crary/819-f09/Moggi91.pdf
https://flint.cs.yale.edu/trifonov/cs629/WadlerMonadsForFP.pdf 

Talk on Relative Monads in CBPV for Stack-based Effects
https://www.youtube.com/watch?v=ooj1vJRixEU

Call by push value guide (basically what we did in class). Figure 4. 
https://dl.acm.org/doi/pdf/10.1145/3537668.3537670

This transformation is “Macro-expressible”. On the Expressive Power of User-Defined Effects 
https://arxiv.org/pdf/1610.09161.pdf 

Future work on Type memory segment pairs as proofs in dependently typed ML.
https://www.cs.bu.edu/~hwxi/atslangweb/MYDATA/VsTsVTs-2018-10-28.pdf 
https://www.cs.bu.edu/~hwxi/atslangweb/MYDATA/SPPSV-padl05.pdf 

