package org.lbee.models;

public enum TwoPhaseMessage {
    Register,
    Prepared,
    Commit,
    Abort;
}