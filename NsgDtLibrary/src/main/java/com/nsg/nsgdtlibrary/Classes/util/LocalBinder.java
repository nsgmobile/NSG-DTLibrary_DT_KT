package com.nsg.nsgdtlibrary.Classes.util;

import android.os.Binder;

/**
 * Class used for the client Binder.  Since this service runs in the same process as its
 * clients, we don't need to deal with IPC.
 */
public class LocalBinder extends Binder {
        LocationUpdatesService service = null;
        void setService(LocationUpdatesService service){
            this.service = service;
        }
        LocationUpdatesService getService() {
            return this.service;
        }
    }