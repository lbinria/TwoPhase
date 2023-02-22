package org.lbee.twophase;

import java.util.ArrayList;
import java.util.List;

public class TLAValue implements IFormalValue<App2TLA.TLAEvent> {

    private String name;
    private final List<App2TLA.TLAEvent> changes;

    public TLAValue() {
        this.changes = new ArrayList<>();
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void apply(String operator, Object value) {
        // TODO add operator, clock or not
        this.changes.add(new App2TLA.TLAEvent(this.name, value.toString(), 0));
    }

    @Override
    public void commit(long clock) {

        for (App2TLA.TLAEvent change : this.changes) {
            change.setClock(clock);
            change.commit();
        }

        this.changes.clear();
    }

}
