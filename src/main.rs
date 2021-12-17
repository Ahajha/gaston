mod types;
mod tid_list;
mod database;

fn main() {
    println!("Hello, world!");
    
    let _db = database::Database::read("", 0);
}
