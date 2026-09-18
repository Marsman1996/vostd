window.BENCHMARK_DATA = {
  "lastUpdate": 1789733679301,
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
      },
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
          "distinct": true,
          "id": "43d520b47870c35c630702e213614ac855b41395",
          "message": "ci: refactor ci workflow",
          "timestamp": "2026-09-14T18:26:05+08:00",
          "tree_id": "4698216f02ae4015fbc1fc7b21cadb69c331271f",
          "url": "https://github.com/Marsman1996/vostd/commit/43d520b47870c35c630702e213614ac855b41395"
        },
        "date": 1789382470778,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1075909141,
            "unit": "rlimit",
            "extra": "verified=4079 errors=0 smt-run=338,618ms wall=219,040ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 369104275,
            "unit": "rlimit",
            "extra": "smt-run=139,439ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 87683492,
            "unit": "rlimit",
            "extra": "smt-run=30,210ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 86123454,
            "unit": "rlimit",
            "extra": "smt-run=30,570ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,731ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,575ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,739ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,142ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=882ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=649ms"
          }
        ]
      },
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
          "distinct": true,
          "id": "8d2a7642134ca98176155130ad51d58a2c507f7b",
          "message": "ci: refactor ci workflow",
          "timestamp": "2026-09-14T19:11:59+08:00",
          "tree_id": "c08b95ac59bf497c8d07852ab30bf4d9dd3c7b6f",
          "url": "https://github.com/Marsman1996/vostd/commit/8d2a7642134ca98176155130ad51d58a2c507f7b"
        },
        "date": 1789384687328,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1075909141,
            "unit": "rlimit",
            "extra": "verified=4079 errors=0 smt-run=228,426ms wall=156,038ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 369104275,
            "unit": "rlimit",
            "extra": "smt-run=90,444ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 87683492,
            "unit": "rlimit",
            "extra": "smt-run=21,888ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 86123454,
            "unit": "rlimit",
            "extra": "smt-run=21,879ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,070ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,516ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,083ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=807ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=564ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=387ms"
          }
        ]
      },
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
          "distinct": true,
          "id": "bfe490143625b8ff1799831a97412e1fd90a397a",
          "message": "ci: refactor ci workflow",
          "timestamp": "2026-09-14T19:38:10+08:00",
          "tree_id": "62b23d132aa5e6975b96de61ddb545ee2223e84e",
          "url": "https://github.com/Marsman1996/vostd/commit/bfe490143625b8ff1799831a97412e1fd90a397a"
        },
        "date": 1789386159315,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1075909141,
            "unit": "rlimit",
            "extra": "verified=4079 errors=0 smt-run=256,879ms wall=174,854ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 369104275,
            "unit": "rlimit",
            "extra": "smt-run=104,130ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 87683492,
            "unit": "rlimit",
            "extra": "smt-run=22,380ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 86123454,
            "unit": "rlimit",
            "extra": "smt-run=22,531ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,191ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,702ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,115ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=946ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=641ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=453ms"
          }
        ]
      },
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
          "distinct": true,
          "id": "4dd7234f7e00b62c2de27b5536a53a7a72efca37",
          "message": "ci: refactor ci workflow",
          "timestamp": "2026-09-14T20:40:16+08:00",
          "tree_id": "fa60f3599aaf3a5dde0b6ae701cdfede92ce97ef",
          "url": "https://github.com/Marsman1996/vostd/commit/4dd7234f7e00b62c2de27b5536a53a7a72efca37"
        },
        "date": 1789389995171,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1070545411,
            "unit": "rlimit",
            "extra": "verified=4079 errors=0 smt-run=259,530ms wall=176,439ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 371411986,
            "unit": "rlimit",
            "extra": "smt-run=109,545ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 86512060,
            "unit": "rlimit",
            "extra": "smt-run=24,918ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 80760641,
            "unit": "rlimit",
            "extra": "smt-run=21,309ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,060ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,523ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,171ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=864ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=561ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=408ms"
          }
        ]
      },
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
          "distinct": true,
          "id": "7ed0a37220b8ee0dd821ce84272b42f37c72bfbb",
          "message": "ci: refactor ci workflow",
          "timestamp": "2026-09-14T21:44:17+08:00",
          "tree_id": "b4a11921d7b99ba606020d5292edcb8a9ef8d446",
          "url": "https://github.com/Marsman1996/vostd/commit/7ed0a37220b8ee0dd821ce84272b42f37c72bfbb"
        },
        "date": 1789393866571,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1070545411,
            "unit": "rlimit",
            "extra": "verified=4079 errors=0 smt-run=328,602ms wall=218,440ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 371411986,
            "unit": "rlimit",
            "extra": "smt-run=136,578ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 86512060,
            "unit": "rlimit",
            "extra": "smt-run=32,094ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 80760641,
            "unit": "rlimit",
            "extra": "smt-run=24,129ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,500ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,404ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,578ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,090ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=762ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=607ms"
          }
        ]
      },
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
          "distinct": true,
          "id": "7e6053c1f61d2823a25cb41cabd3da63ceaa920a",
          "message": "ci: parallelize doc build",
          "timestamp": "2026-09-18T19:58:06+08:00",
          "tree_id": "c7523cd01106af7920af0d0754c7eaf7d7d68f8d",
          "url": "https://github.com/Marsman1996/vostd/commit/7e6053c1f61d2823a25cb41cabd3da63ceaa920a"
        },
        "date": 1789733678271,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1039768479,
            "unit": "rlimit",
            "extra": "verified=4050 errors=0 smt-run=259,122ms wall=177,653ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 331983855,
            "unit": "rlimit",
            "extra": "smt-run=98,380ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 107410625,
            "unit": "rlimit",
            "extra": "smt-run=29,005ms"
          },
          {
            "name": "rlimit: specs::mm::embedding",
            "value": 48459213,
            "unit": "rlimit",
            "extra": "smt-run=17,530ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,648ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,129ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,345ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=936ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1990774,
            "unit": "rlimit",
            "extra": "smt-run=654ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=457ms"
          }
        ]
      }
    ]
  }
}