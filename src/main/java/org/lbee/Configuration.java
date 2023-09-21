package org.lbee;

import java.util.Random;

public class Configuration {

    public int nResourceManager = 2;
    public TransactionManagerConfiguration tmConfig;
    public ResourceManagerConfiguration rmConfig;

    public Configuration(final String[] args) {
        this.tmConfig = new TransactionManagerConfiguration(nResourceManager, Integer.MAX_VALUE);
        this.rmConfig = new ResourceManagerConfiguration(false, -1);
    }

    @Override
    public String toString() {
        return "Configuration{" +
                "transactionManagerConfig=" + tmConfig +
                ", resourceManagerConfig=" + rmConfig +
                '}';
    }

}

/**
 * Configuration of a resource manager
 * @param shouldFail Is resource manager should fail, invoke an unknown exception
 * @param taskDuration Duration of the simulated task
 */
record ResourceManagerConfiguration(boolean shouldFail, int taskDuration) {

    ResourceManagerConfiguration(boolean shouldFail, int taskDuration) {
        this.shouldFail = shouldFail;

        if (taskDuration == -1)
            /* Set a random task duration */
            //this.taskDuration = new Random().nextInt(10000);
            this.taskDuration = new Random().nextInt(100);
        else
            this.taskDuration = taskDuration;
    }

    @Override
    public String toString() {
        return "ResourceManagerConfiguration{" +
                "shouldFail=" + shouldFail +
                ", taskDuration=" + taskDuration +
                '}';
    }
}

/**
 * Configuration of a resource manager
 * @param timeout Is resource manager should fail, invoke an unknown exception
 */
record TransactionManagerConfiguration(int nResourceManager, int timeout) {
    @Override
    public String toString() {
        return "TransactionManagerConfiguration{" +
                "timeout=" + timeout +
                '}';
    }
}