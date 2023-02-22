package org.lbee.twophase;

import jdk.jfr.Category;
import jdk.jfr.Label;
import jdk.jfr.Name;
import jdk.jfr.StackTrace;

import java.util.List;

public class App2TLA {

    @Label("TLAEvent")
    @Name("app.TLAEvent")
    @Category("TwoPhase")
    @StackTrace(false)
    static class TLAEvent extends jdk.jfr.Event implements CommitEvent {

        @Label("clock")
        long clock;
        @Label("key")
        String key;
        @Label("val")
        String val;

        public TLAEvent(String key, Object val, long clock) {
            this.clock = clock;
            this.key = key;
            this.val = val.toString();
            System.out.printf("Log event %s = %s.\n", key, val.toString());
        }

        public void setClock(long clock) {
            this.clock = clock;
        }

    }

}
