use bend::{
  diagnostics::Diagnostics,
  fun::{load_book::load_to_book, Book, Name},
};
use bpm::*;
use clap::Subcommand;
use std::path::PathBuf;

use crate::CliWarnOpts;

#[derive(Subcommand, Clone, Debug)]
pub enum PackageCmd {
  /// Stores a bend file into the package manager
  Store {
    #[arg(help = "Path to the input file")]
    path: PathBuf,
    #[arg(
      short = 'n',
      long = "name",
      help = "Overwrite the name of the package, otherwise the file name is used"
    )]
    name: Option<String>,
    #[arg(help = "Namespace to store the file")]
    namespace: String,
    #[arg(help = "Version of the package", default_value = "v0")]
    version: String,
  },
  /// Loads a package from the package manager
  Load {
    #[arg(help = "Name of the package to load")]
    name: String,
  },
  /// Checks fo permissions to create/update the target package
  CanPost {
    #[arg(help = "Name of the package to check for permissions")]
    name: String,
  },
  /// Adds permissions to update the target package to the given user name
  AddPerms {
    #[arg(help = "Name of the package/namespace to modify the permissions")]
    name: String,
    #[arg(help = "Username to add the edit/create permissions to")]
    user: String,
  },
  /// Makes a namespace public, allowing all users to create packages inside
  MakePub {
    #[arg(help = "Name of the namespace to make public")]
    name: String,
  },
  /// Register a new Bend Package Manager account
  Register,
}

pub fn handle_package_cmd(command: PackageCmd) -> Result<(), Diagnostics> {
  match command {
    PackageCmd::CanPost { name } => match can_post(&PackageDescriptor::from(name.as_str())) {
      Ok(true) => println!("The package {name} can be uploaded"),
      Ok(false) => println!("The package {name} can NOT be uploaded"),
      err @ Err(_) => _ = err?,
    },

    PackageCmd::AddPerms { name, user } => add_perms(PackageDescriptor::from(name.as_str()), User(user))?,

    PackageCmd::Store { path, name, namespace, version } => store_cmd(path, name, namespace, version)?,

    PackageCmd::Load { name } => load_cmd(&name).map(|pack| println!("{}", pack))?,

    PackageCmd::MakePub { name } => make_public(name)?,

    PackageCmd::Register => register_cmd()?,
  };

  Ok(())
}

fn store_cmd(
  path: PathBuf,
  name: Option<String>,
  namespace: String,
  version: String,
) -> Result<(), Diagnostics> {
  let package_name = match name {
    Some(name) => format!("{}/{}", namespace, name),
    None => {
      let path = path.clone().with_extension("");
      let file_name = path.file_name();
      let file_name = file_name.ok_or("Expected a file path to Store, found a directory".to_string())?;
      format!("{}/{}", namespace, file_name.to_string_lossy())
    }
  };

  let pack = PackageDescriptor::new(Some(&version), &package_name);
  let package = check(path)?;
  store(pack, package)?;

  Ok(())
}

pub fn load_cmd(name: &str) -> Result<String, String> {
  load(&PackageDescriptor::from(name)).map(|Package(pack)| pack)
}

pub fn load_multiple(name: &Name, sub_packages: &[Name]) -> Result<String, String> {
  if sub_packages.is_empty() { load_cmd(name) } else { todo!() }
}

fn check(path: PathBuf) -> Result<Package, Diagnostics> {
  let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;

  let load_book = |mut path: std::path::PathBuf| -> Result<Book, Diagnostics> {
    let mut book = load_to_book(path.display(), &source, load_multiple)?;
    path.set_extension("");
    book.entrypoint = path.file_name().map(|e| Name::new(e.to_string_lossy()));
    Ok(book)
  };

  crate::check(CliWarnOpts::default(), Vec::new(), load_book, path)?;

  Ok(Package(source))
}

fn register_cmd() -> Result<(), String> {
  use std::io::{stdout, Write};

  print!("Please enter your username: ");
  let _ = stdout().flush();

  let user = get_input();

  loop {
    print!("Please enter your password:  ");
    let _ = stdout().flush();
    let pass = rpassword::read_password().unwrap();

    print!("Please repeat your password: ");
    let _ = stdout().flush();
    let pass2 = rpassword::read_password().unwrap();

    if pass != pass2 {
      println!("Passwords do not match, please try again")
    } else {
      register_user(&user, &pass)?;
      println!("User `{user}` registered");
      return Ok(());
    }
  }
}

fn get_input() -> String {
  use std::io::stdin;

  let mut user = String::new();
  stdin().read_line(&mut user).expect("Did not enter a correct string");

  if let Some('\n') = user.chars().next_back() {
    user.pop();
  }

  if let Some('\r') = user.chars().next_back() {
    user.pop();
  }

  user
}