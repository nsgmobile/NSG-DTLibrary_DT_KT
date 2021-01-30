package com.nsg.nsgdtlibrary.Classes.util;

import android.os.AsyncTask;
import android.util.Log;

import static com.nsg.nsgdtlibrary.Classes.util.Utils.HttpPost;

public class DownloadRouteFromURL extends AsyncTask<String, String, String> {

        public AsyncResponse delegate = null;//Call back interface

        private String routeDeviatedDT_URL;
        private String authorisationKey;

        public DownloadRouteFromURL(AsyncResponse asyncResponse, String routeDeviatedDT_URL, String authorisationKey) {
            delegate = asyncResponse;//Assigning call back interfacethrough constructor
            this.authorisationKey = authorisationKey;
            this.routeDeviatedDT_URL = routeDeviatedDT_URL;
        }

    @Override
        protected void onPostExecute(String result) {
            if (delegate != null) {
                delegate.processFinish(result);
            }
        }

        @Override
        protected void onPreExecute() {
            super.onPreExecute();
        }

        @Override
        protected String doInBackground(String... params) {
            try {
                String param1, param2;
                param1 = params[0];
                param2 = params[1];
                return HttpPost(routeDeviatedDT_URL, param1, param2, authorisationKey);

            } catch (Exception e) {
                Log.e("doInBackground", e.getMessage(), e);
            }
            return null;
        }

        protected void onProgressUpdate(String... progress) {
        }
    }