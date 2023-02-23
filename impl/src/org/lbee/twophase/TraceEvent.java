package org.lbee.twophase;

public interface TraceEvent {

    void setSender(String sender);
    void setClock(long clock);
    void commit();

}
