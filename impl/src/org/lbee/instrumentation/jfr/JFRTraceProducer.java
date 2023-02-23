package org.lbee.instrumentation.jfr;

import org.lbee.instrumentation.TraceProducer;

public class JFRTraceProducer implements TraceProducer<JFRTraceEvent> {

    @Override
    public JFRTraceEvent produce(String operator, String name, Object value, long clock) {
        System.out.printf("%s - Trace event: `%s %s (%s)`.\n", clock, operator, name, value.toString());
        return new JFRTraceEvent(operator, name, value.toString(), clock);
    }

}
