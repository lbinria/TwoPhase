package org.lbee.instrumentation.jfr;

import org.lbee.instrumentation.FormalInstrumentation;
import org.lbee.instrumentation.TraceEvent;
import org.lbee.instrumentation.TraceProducer;

import java.util.ArrayList;
import java.util.List;

// @TraceProducer(name="JFR")
public class JFRTraceProducer implements TraceProducer<JFRTraceEvent> {

    private FormalInstrumentation<?> instrumentation;
    private final List<TraceEvent> traces;

    public JFRTraceProducer() {
        this.traces = new ArrayList<>();
    }

    public void setIntrumentation(FormalInstrumentation<?> instrumentation) {
        this.instrumentation = instrumentation;
    }

    @Override
    public void commit(long clock) {

        for (TraceEvent trace : this.traces) {
            trace.setClock(clock);
            trace.commit();
        }

        this.traces.clear();
    }

    @Override
    public JFRTraceEvent produce(String operator, String name, Object value, String type, long clock) {
        System.out.printf("%s - Trace event: `%s %s (%s)`.\n", clock, operator, name, value.toString());
        JFRTraceEvent trace = new JFRTraceEvent(this.instrumentation.getGuid(), operator, name, value.toString(), type, clock);
        this.traces.add(trace);
        return trace;
    }

}
