use Cwd qw(abs_path);

my $shared_dir = 'Continuum Limit Drafts';
my $shared = abs_path(-d $shared_dir ? $shared_dir : "../$shared_dir");
ensure_path('TEXINPUTS', $shared);
ensure_path('BIBINPUTS', $shared);
