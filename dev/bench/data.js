window.BENCHMARK_DATA = {
  "lastUpdate": 1789189907830,
  "repoUrl": "https://github.com/Marsman1996/vostd",
  "entries": {
    "verify-perf": [
      {
        "commit": {
          "author": {
            "email": "lqliuyuwei@outlook.com",
            "name": "Marsman1996",
            "username": "Marsman1996"
          },
          "committer": {
            "email": "lqliuyuwei@outlook.com",
            "name": "Marsman1996",
            "username": "Marsman1996"
          },
          "distinct": false,
          "id": "24d026502b2a74f3d3f28b1e0c8835a017d8ccf8",
          "message": "ci: chart verus verify cost on in-repo gh-pages + rlimit alerts",
          "timestamp": "2026-09-12T12:47:37+08:00",
          "tree_id": "3c1dbee7a829b7180689b3d1fab09bfbf9c1fdef",
          "url": "https://github.com/Marsman1996/vostd/commit/24d026502b2a74f3d3f28b1e0c8835a017d8ccf8"
        },
        "date": 1789189907213,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1617456838,
            "unit": "rlimit",
            "extra": "verified=4080 errors=0 smt-run=368,533ms wall=221,628ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 752109709,
            "unit": "rlimit",
            "extra": "smt-run=174,632ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 202464146,
            "unit": "rlimit",
            "extra": "smt-run=29,871ms"
          },
          {
            "name": "rlimit: specs::mm::embedding",
            "value": 130778633,
            "unit": "rlimit",
            "extra": "smt-run=57,716ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=992ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9250300,
            "unit": "rlimit",
            "extra": "smt-run=1,490ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,098ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=784ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=518ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=361ms"
          }
        ]
      }
    ]
  }
}