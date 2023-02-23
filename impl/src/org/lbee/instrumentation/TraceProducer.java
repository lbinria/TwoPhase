package org.lbee.instrumentation;

public interface TraceProducer<TOut extends TraceEvent> {

    TOut produce(String op, String name, Object value, long clock);

}
