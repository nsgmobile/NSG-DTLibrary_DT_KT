package com.nsg.nsgdtlibrary.Classes.util;

import com.google.android.gms.location.LocationCallback;
import com.google.android.gms.location.LocationResult;

public class CustomLocationCallback extends LocationCallback {
    private LocationUpdatesService locationUpdatesService;
    public CustomLocationCallback(LocationUpdatesService locationUpdatesService) {
        this.locationUpdatesService = locationUpdatesService;
    }

    public void setLocationUpdatesService(LocationUpdatesService locationUpdatesService) {
        this.locationUpdatesService = locationUpdatesService;
    }

    @Override
    public void onLocationResult(LocationResult locationResult) {
        super.onLocationResult(locationResult);
        if(locationUpdatesService != null) {
            locationUpdatesService.onNewLocation(locationResult.getLastLocation());
        }

    }
}
