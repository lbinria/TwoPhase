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
    @Label("op")
    String op;
    @Label("var")
    String var;
    @Label("args")
    String args;
    @Label("clock")
    long clock;

    public JFRTraceEvent(String sender, String operator, String variableName, String args, long clock) {
        this.sender = sender;
        this.op = operator;
        this.var = variableName;
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
