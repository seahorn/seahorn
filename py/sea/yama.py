import sys
import sea

class Yama(sea.CliCmd):
    def __init__(self):
        super().__init__('yama', 'Yama', allow_extra=False)
        self._ignore_error = False

    def mk_arg_parser(self, argp):
        import argparse
        argp = super().mk_arg_parser(argp)

        argp.add_argument("-y", dest='yconfig', action='append',
                          help="Configuration file", nargs=1)
        argp.add_argument('--dry-run', action='store_true', default=False,
                          help='do not execute final command')
        argp.add_argument('--yforce', action='store_true', default=False,
                          help='ignore all errors')
        argp.add_argument('extra', nargs=argparse.REMAINDER)
        return argp

    def parse_yaml_options(self, fname):
        import yaml
        try:
            with open(fname) as f:
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

            print("Error: no proper sea_options dictionary found in {0}".format(fname))
            sys.exit(1)
            return None
        except:
            if self._ignore_error:
                return None
            print("Error: could not parse", fname)
            sys.exit(1)

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

        # convert value to a string or None if it is not used (including empty string)
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

    def run(self, args = None, _extra = []):
        import sys
        import os

        self._ignore_error = args.yforce
        # set default value
        if args.yconfig is None:
            args.yconfig = [['sea.yaml']]

        extra = args.extra
        args_dict = None
        for f in args.yconfig:
            assert(len(f) == 1)
            yaml_args = self.parse_yaml_options(f[0])
            if yaml_args is None:
                continue
            if args_dict is None:
                args_dict = yaml_args
            else:
                args_dict.update(yaml_args)

        cli = list()
        if args_dict is not None:
            command, cli = self.mk_cli_from_dict(args_dict)

        # override command if specified on command line
        if len(extra) > 0 and not extra[0].startswith('-'):
            command = extra[0]
            extra = extra[1:]

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

