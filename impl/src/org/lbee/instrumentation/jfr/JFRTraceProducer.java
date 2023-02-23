package org.lbee.instrumentation.jfr;

import org.lbee.instrumentation.TraceProducer;

public class JFRTraceProducer implements TraceProducer<App2TLA.TLAEvent> {

    @Override
    public App2TLA.TLAEvent produce(String operator, String name, Object value, long clock) {
        System.out.printf("%s - Trace event: `%s %s (%s)`.\n", clock, operator, name, value.toString());
        return new App2TLA.TLAEvent(operator, name, value.toString(), clock);
    }

}
