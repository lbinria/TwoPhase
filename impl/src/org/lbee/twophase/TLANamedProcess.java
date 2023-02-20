package org.lbee.twophase;

public interface TLANamedProcess {

    LogicalClock getClock();
    String getName();
}
