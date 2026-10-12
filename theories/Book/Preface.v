(** * Preface

    This executable book accompanies the first three chapters of Hanpin
    Wang's _Mathematical Logic (Discrete Mathematics, Volume I)_.  Its goal is
    not to replace the mathematical text.  Instead, it gives the definitions
    and proof systems a second, machine-checkable presentation that students
    can inspect one sentence at a time in VSRocq.

    The development is deliberately small.  Formulas are ordinary Rocq data,
    valuations are executable functions, and derivability judgments are
    inductive families whose inhabitants are proof trees.  We formalize the
    structural lemmas needed in class, but leave large soundness and
    completeness developments outside the first version of the course.

    ** How to read this book

    Each chapter mixes prose with live Rocq commands.  Open the corresponding
    [.v] file, put the cursor after a command, and select _Interpret to Point_.
    The Goals panel then shows exactly the state described by the text.  A
    [Compute] command is an invitation to predict the result before asking
    Rocq to evaluate it.

    ** Exercises

    Exercises are labelled by difficulty.  One star means direct use of a
    definition or inference rule; two stars require a short proof plan; three
    stars normally combine several earlier ideas.  Representative solutions
    are public, while the chapter worksheets intentionally retain holes for
    students.

    ** Language and notation

    Explanatory prose is in English.  Chinese names used in the textbook are
    recorded alongside important results.  Rocq identifiers remain in English
    so that error messages, editor search, and library documentation use one
    stable vocabulary. *)

(** The file contains documentation only.  Rocq accepts such a chapter as a
    valid compilation unit, which lets it participate in the same build and
    HTML pipeline as the formal chapters. *)
