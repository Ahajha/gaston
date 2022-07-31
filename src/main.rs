mod database;
mod tid_list;
mod types;

fn main() {
    println!("Hello, world!");

    let db = database::Database::read("", 0);

    match db {
        Ok(db) => println!("{:?}", db),
        Err(err) => println!("{}", err),
    };
}
