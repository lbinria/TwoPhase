package org.lbee.twophase;

import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class App {

    public static void main(String[] args) throws InterruptedException, IOException {

        final Configuration config = new Configuration(args);

        // Some printing
        System.out.println(config);
        System.out.println("Start...");

        // TODO In order to make a consistent total log file, we have to synchronize global clocks of processes !
        // We send current clock reference to all processes and compute delta for each process

        // Create a transaction manager
        final TransactionManager transactionManager = new TransactionManager(config.transactionManagerConfig);
        /* Create collection of tasks */
        final Collection<Callable<Void>> tasks = new HashSet<>();
        tasks.add(transactionManager);

        for (int i = 0; i < config.nResourceManager; i++) {
            // Create a resource manager
            final ResourceManager resourceManager = new ResourceManager("rm" + (i + 1), transactionManager, config.resourceManagerConfig[i]);
            // Add resource manager as task to run
            tasks.add(resourceManager);
            transactionManager.addResourceManager(resourceManager);
        }

        // Run all tasks concurrently.
        final ExecutorService pool = Executors.newCachedThreadPool();
        pool.invokeAll(tasks);

        // transactionManager.abort();

        pool.shutdown();
        pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);

        System.out.println("End.");

    }

    /* Stolen from lemmy */
    private static class Configuration {

        public int nResourceManager = 2;
        public TransactionManager.TransactionManagerConfiguration transactionManagerConfig;
        public ResourceManager.ResourceManagerConfiguration[] resourceManagerConfig;

        public Configuration(String args[]) {
            this.transactionManagerConfig = new TransactionManager.TransactionManagerConfiguration(1200);
            this.resourceManagerConfig = new ResourceManager.ResourceManagerConfiguration[this.nResourceManager];
            for (int i = 0; i < this.nResourceManager; i++) {
                this.resourceManagerConfig[i] = new ResourceManager.ResourceManagerConfiguration(false, -1);
            }
        }

        @Override
        public String toString() {
            return "Configuration{" +
                    "transactionManagerConfig=" + transactionManagerConfig +
                    ", resourceManagerConfig=" + resourceManagerConfig +
                    '}';
        }
    }

}
