from distutils.core import setup


setup(
  name = 'amr2fol',
  packages = ['amr2fol'],
  version = '0.3.1',
  description = 'Transform Abstract Meaning Representation (AMR) annotations to First Order Logic (FOL) formulas.',
  author = 'Marcos Pertierra',
  author_email = 'marcosp@mit.edu',
  url = 'https://github.com/mpertierra/amr2fol.git',
  download_url = 'https://github.com/mpertierra/amr2fol/archive/0.3.1.tar.gz',
  keywords = ['amr', 'logic', 'fol', 'semantics', 'nlp'],
  classifiers = [],
  install_requires = [
    'appdirs>=1.4.3',
    'docopt>=0.6.2',
    'nltk>=3.2.2',
    'packaging>=16.8',
    'Penman>=0.6.1',
    'pyparsing>=2.2.0',
    'six>=1.10.0'
  ]
)