import sys

import sea


class Yama(sea.CliCmd):
    def __init__(self):
        super().__init__('yama', 'Yama', allow_extra=False)
        self._ignore_error = False
        self._used_profile = False

    def mk_arg_parser(self, argp):
        import argparse
        argp = super().mk_arg_parser(argp)

        argp.add_argument("-y", dest='yconfig', action='append',
                          help="Configuration file, URL, or the name of a "
                          "profile (NAME.yaml in $SEAHORN_PROFILE_PATH, "
                          "then in <prefix>/share/seahorn/profiles)",
                          nargs=1)
        argp.add_argument('--dry-run', action='store_true', default=False,
                          help='do not execute final command')
        argp.add_argument('--yforce', action='store_true', default=False,
                          help='ignore all errors')
        argp.add_argument('--ylead-opts', dest='ylead_opts',
                          action='store_true', default=False,
                          help='pass on options given before the first '
                          'non-option word (e.g. `sea yama -y P --bound=8 '
                          'prog.bc`); without it they are dropped, except '
                          'when a -y names a shipped profile')
        argp.add_argument('extra', nargs=argparse.REMAINDER)
        return argp

    @staticmethod
    def profile_dirs():
        """Directories searched for a profile given by name: the entries of
        $SEAHORN_PROFILE_PATH (colon-separated), then the profiles shipped
        with SeaHorn (<prefix>/share/seahorn/profiles, <prefix> being the
        parent of the directory of the sea script)."""
        import os
        dirs = [d for d in os.environ.get('SEAHORN_PROFILE_PATH', '').split(':')
                if d]
        bindir = os.path.dirname(os.path.abspath(sys.argv[0]))
        dirs.append(os.path.join(bindir, '..', 'share', 'seahorn', 'profiles'))
        return dirs

    def resolve_config(self, fname):
        """A -y argument names a file or URL; if it is neither an existing
        file nor a URL and has no '/', it is the name of a profile, looked up
        as NAME.yaml (or NAME, if it already ends in .yaml) in
        profile_dirs(). Returns the path to read (fname if nothing is found:
        the error is reported when it is read)."""
        import os
        import urllib.parse
        if os.path.isfile(fname) or '/' in fname:
            return fname
        url = urllib.parse.urlparse(fname)
        if url.scheme is not None and len(url.scheme) > 0:
            return fname
        base = fname if fname.endswith('.yaml') else fname + '.yaml'
        for d in self.profile_dirs():
            path = os.path.join(d, base)
            if os.path.isfile(path):
                path = os.path.normpath(path)
                print('Yama using profile {0}: {1}'.format(fname, path))
                self._used_profile = True
                return path
        if not self._ignore_error:
            print('Yama: no file or profile named {0} (profiles searched in: '
                  '{1})'.format(fname, ', '.join(os.path.normpath(d)
                                                 for d in self.profile_dirs())))
        return fname

    def parse_yaml_options(self, fname):
        import urllib.parse
        import urllib.request

        import yaml
        try:
            data = dict()

            url = urllib.parse.urlparse(fname)
            if url.scheme is not None and len(url.scheme) > 0:
                with urllib.request.urlopen(fname) as f:
                    data = yaml.load(f, Loader=yaml.SafeLoader)
            else:
                with open(fname, 'r') as f:
                    data = yaml.load(f, Loader=yaml.SafeLoader)

            # common containers for options
            if 'verify_options' in data:
                data = data['verify_options']
            elif 'sea_options' in data:
                data = data['sea_options']
            elif 'sea_arguments' in data:
                data = data['sea_arguments']
            else:
                data = None

            if data is not None and isinstance(data, dict):
                return data
            if self._ignore_error:
                return None

            print("Error: no proper sea_options " +
                  "dictionary found in {0}".format(fname))
            sys.exit(1)
            return None
        except Exception:
            if self._ignore_error:
                return None
            print("Error: could not parse", fname)
            sys.exit(1)

    def parse_extra_options(self, extra):
        args = dict()
        positional = list(filter(lambda x: not x.startswith('-'), extra))
        flags = list(filter(lambda x: x.startswith('-'), extra))

        for kv in flags:
            # strip '--' if present
            if kv.startswith('--'):
                kv = kv[2:]
            # attempt to split into key, value pair
            kvs = kv.split('=')
            # use pair if successful, and original option otherwise
            if len(kvs) == 2:
                args[kvs[0]] = kvs[1]
            else:
                args[kv] = ''

        return args, positional

    def mk_cli_from_key_value(self, _key, _value):
        """
        Convert (key, value) pair into a command line option
        """
        short_arg = False
        key = str(_key)
        # if key starts with a dash, it is a short form of an argument
        if key.startswith('-'):
            short_arg = True
        else:
            key = '--' + str(_key)
            short_arg = False

        # convert value to a string or None if it is not used (including empty
        # string)
        value = str(_value) if _value is not None else None
        if value is not None and len(value) == 0:
            value = None
        if isinstance(_value, bool):
            value = value.lower()

        # short argument
        if value is not None and short_arg:
            return '{k} {v}'.format(k=key, v=value)
        # long argument
        elif value is not None and not short_arg:
            return '{k}={v}'.format(k=key, v=value)
        # flag only argument
        else:
            return key

    def mk_cli_from_dict(self, arg_dict):
        res = []
        command = None
        for key, value in arg_dict.items():
            if key == 'command':
                command = value
            else:
                res.append(self.mk_cli_from_key_value(key, value))

        return command, res

    def run(self, args=None, _extra=[]):
        import os
        import os.path
        import sys

        self._ignore_error = args.yforce
        # set default value
        if args.yconfig is None:
            args.yconfig = [['sea.yaml']]

        # resolve -y arguments first: naming a shipped profile turns on
        # --ylead-opts below
        configs = [self.resolve_config(f[0]) for f in args.yconfig]

        # options before the first non-option word (e.g. `sea yama -y P
        # --bound=8 prog.bc`, the sub-command coming from the profile) are
        # not part of args.extra: the top-level `sea` parser hands them over
        # as _extra. They are dropped (old behavior) unless --ylead-opts is
        # given or a -y named a shipped profile.
        extra = args.extra
        if args.ylead_opts or self._used_profile:
            extra = list(_extra) + args.extra
        args_dict = None
        for f, fname in zip(args.yconfig, configs):
            assert len(f) == 1
            yaml_args = self.parse_yaml_options(fname)
            if yaml_args is None:
                continue
            if args_dict is None:
                args_dict = yaml_args
            else:
                args_dict.update(yaml_args)

        extra_cli_args, extra = self.parse_extra_options(extra)
        if args_dict is None:
            args_dict = extra_cli_args
        else:
            args_dict.update(extra_cli_args)

        cli = list()
        if args_dict is not None:
            command, cli = self.mk_cli_from_dict(args_dict)

        # override command if specified on command line
        # but ignore files
        if len(extra) > 0 and not extra[0].startswith('-') and \
           not os.path.isfile(extra[0]):
            command = extra[0]
            extra = extra[1:]

        if command is None:
            print('Error: no sea sub-command specified. Use pf, bpf, ...',
                  file=sys.stderr)
            return 1

        cmd_args = []
        cmd_args.append(sys.argv[0])
        cmd_args.append(command)
        if len(cli) > 0:
            cmd_args.extend(cli)
        cmd_args.extend(extra)

        print('Yama executing command:')
        print(' '.join(cmd_args))

        sys.stdout.flush()
        sys.stderr.flush()
        if args.dry_run:
            return 0
        os.execl(sys.executable, sys.executable, *cmd_args)
        # unreachable, unless there is an error
        return 1
