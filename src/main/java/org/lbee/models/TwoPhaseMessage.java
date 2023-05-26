package org.lbee.models;

public enum TwoPhaseMessage {
    // using the constructor defined below
    REGISTER("Register"),
    PREPARED("Prepared"),
    COMMIT("Commit"),
    ABORT("Abort");

    // Member to hold the name
    private final String string;

    // constructor to set the string
    TwoPhaseMessage(final String name) { string = name; }

    // the toString just returns the given name
    @Override
    public final String toString() {
        return string;
    }
}