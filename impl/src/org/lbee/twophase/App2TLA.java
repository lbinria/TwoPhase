package org.lbee.twophase;

import jdk.jfr.Category;
import jdk.jfr.Label;
import jdk.jfr.Name;
import jdk.jfr.StackTrace;

public class App2TLA {

    @Label("TLAEvent")
    @Name("app.TLAEvent")
    @Category("TwoPhase")
    @StackTrace(false)
    static class TLAEvent extends jdk.jfr.Event implements TraceEvent {

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

        public TLAEvent(String operator, String key, Object val, long clock) {
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

}
