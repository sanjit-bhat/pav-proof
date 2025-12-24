- this project formally verifies the pav Key Transparency system,
written in golang.
- it uses the perennial framework, built on iris and stdpp,
which is built on the rocq theorem prover.
many of these deps have been added as claude working directories.
- "new" perennial proofs have three main directories:
    - `code/`: Goosed (compiled) golang code.
    - `generatedproof/`: auto-generated proofs.
    you will never need to reference these; they're automatically applied.
    - `proof/`: proofs (usually WP-style lemmas) about the code.
- do not run the rocq compiler.
- if you aren't confident about something, it's perfectly fine to say that.
there isn't much rocq / iris code out there to learn from.
