package org.lbee.protocol;

public enum TwoPhaseMessage {
    Register,
    Prepared,
    Commit,
    Abort;
}