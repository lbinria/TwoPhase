package org.lbee.twophase;

public interface TraceEvent {

    void setClock(long clock);
    void commit();

}
