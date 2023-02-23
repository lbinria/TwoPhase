package org.lbee.twophase;

public interface FormalValue<TProducer extends TraceProducer> {

    void setName(String name);
    void apply(String operator, Object value);
    void commit(long clock);

}
