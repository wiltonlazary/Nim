import db_sqlite

let db = open(connection="sighashes.db", user="araq", password="",
              database="sighashes")
db.exec(sql"Drop table if exists sighashes")
db.exec(sql("""create table sighashes (
     id    INTEGER PRIMARY KEY,
     type  VARCHAR(5000) NOT NULL,
     hash  VARCHAR(5000) NOT NULL,
     UNIQUE(type, hash))"""))
db.close()
