from setuptools import setup
setup(
    name = 'sea',
    version = '0.1',
    packages = ['sea'],
    
    entry_points = {
        'setuptools.installation': [
            'eggsecutable = sea:__main__',
        ]
    },
    
    author = 'Arie Gurfinkel',
    author_email = "arie@cmu.edu",
    description = "SeaHorn Verification Framework",
    license = "BSD",
    keywords = "verification model-checking static-analysis horn",
    url = "http://seahorn.github.io",   
)
