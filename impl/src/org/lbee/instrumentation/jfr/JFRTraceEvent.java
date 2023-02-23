package org.lbee.instrumentation.jfr;

import jdk.jfr.Category;
import jdk.jfr.Label;
import jdk.jfr.Name;
import jdk.jfr.StackTrace;
import org.lbee.instrumentation.TraceEvent;

@Label("JFRTraceEvent")
@Name("app.JFRTraceEvent")
@Category("TraceValidation")
@StackTrace(false)
public class JFRTraceEvent extends jdk.jfr.Event implements TraceEvent {

    @Label("sender")
    String sender;
    @Label("key")
    String key;
    @Label("op")
    String op;
    @Label("val")
    String val;
    @Label("clock")
    long clock;

    public JFRTraceEvent(String operator, String key, Object val, long clock) {
        this.op = operator;
        this.key = key;
        this.val = val.toString();
        this.clock = clock;
    }

    public void setClock(long clock) {
        this.clock = clock;
    }

    public void setSender(String sender) {
        this.sender = sender;
    }

}
