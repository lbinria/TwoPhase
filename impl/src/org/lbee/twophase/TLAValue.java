package org.lbee.twophase;

import java.util.ArrayList;
import java.util.List;

public class TLAValue implements FormalValue<JFRTraceProducer> {

    private String name;
    private final List<TraceEvent> traces;
    private final JFRTraceProducer traceProducer;

    public TLAValue() {
        this.traces = new ArrayList<>();
        this.traceProducer = new JFRTraceProducer();
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void apply(String operator, Object value) {
        TraceEvent trace = traceProducer.produce(operator, this.name, value.toString(), 0);
        this.traces.add(trace);
    }

    @Override
    public void commit(long clock) {

        for (TraceEvent trace : this.traces) {
            trace.setClock(clock);
            trace.commit();
        }

        this.traces.clear();
    }

}
