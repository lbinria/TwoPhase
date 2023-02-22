package org.lbee.twophase;

import java.util.List;

public interface IFormalValue<T extends CommitEvent> {

    void setName(String name);
    void apply(String operator, Object value);
    void commit(long clock);

}
