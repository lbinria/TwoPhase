---- MODULE Apply ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags
CONSTANTS VarTypes
ASSUME VarTypes \in {"unstructured", "record", "set", "seq", "bag"}

Apply(name, var, val) ==
    IF val.op = "=" THEN
        var' = val.val
    ELSE IF VarTypes[name] = "record" THEN
        IF val.op = "+" THEN
            (* Function append *)
            var' = [var EXCEPT ![val.val.key] = val.val.val]
        ELSE
            var' = val.val
    ELSE IF VarTypes[name] = "set" THEN
        (* Set union *)
        IF val.op = "+" THEN
            var' = var \cup val.val
        (* Set diff *)
        ELSE IF val.op = "-" THEN
            var' = var \ val.val
        ELSE
            var' = val.val
    ELSE IF VarTypes[name] = "seq" THEN
        (* Sequence add element *)
        IF val.op = "+" THEN
            var' = var \o val.val
        (* Sequence remove element (TODO check if notin works with sequences <<>>) *)
        ELSE IF val.op = "-" THEN
            var' = SelectSeq(var, LAMBDA x: x \notin val.val)
        ELSE
            var' = val.val
    ELSE IF VarTypes[name] = "bag" THEN
        (* Bag append *)
        IF val.op = "+" THEN
            var' = var (+) val.val
        (* Bag remove *)
        ELSE IF val.op = "-" THEN
            var' = var (-) val.val
        ELSE
            var' = val.val
    ELSE
        var' = var
====
