package org.lbee.instrumentation;

public interface TraceEvent {

    void setSender(String sender);
    void setClock(long clock);
    void commit();

}
