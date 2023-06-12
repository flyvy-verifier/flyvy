# Running flyvy on AWS

## Creating an image

Set up an image (once) with Z3 precompiled:

Start a z1d.xlarge instance (or z1d.2xlarge for faster compilation). Make sure
to set a key pair and a rule that allows ssh access. This cannot be spot
instance, but we'll only have it run for a short time.

SSH to the instance:
```
export ip=...
ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no ec2-user@$ip
```

Run `wget
https://raw.githubusercontent.com/vmware-research/temporal-verifier/qalpha/tools/setup-aws.sh`
followed by `bash setup-aws.sh`. This should take 10 minutes (less on bigger machine).

When this finishes, create an AMI from the instance:

Stop instance

Select instance and click on Actions > Images and templates > Create image

This takes some time due to creating a snapshot. When the AMI status is
"Available", terminate the instance used to create the image.

## Using the image

Launch an instance from the AMI page. Set its instance type (z1d.xlarge or
z1d.2xlarge), give it a name, select a key pair and access control, and under
Advanced make it a Spot instance.

SSH to the instance (same as above) and run the following:

```
cd temporal-verifier
git pull
cargo build --release
```
