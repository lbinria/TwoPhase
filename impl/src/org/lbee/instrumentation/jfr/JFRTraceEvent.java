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
    @Label("args")
    String args;
    @Label("clock")
    long clock;

    public JFRTraceEvent(String sender, String operator, String key, String args, long clock) {
        this.sender = sender;
        this.op = operator;
        this.key = key;
        this.args = args;
        this.clock = clock;
    }

    public void setClock(long clock) {
        this.clock = clock;
    }

    public void setSender(String sender) {
        this.sender = sender;
    }

}
